-- Prove2me | Theorems.Thm_QIndInf_cumulative_squared_error_le
-- name    : QIndInf.cumulative_squared_error_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:30:44.058865+00:00
-- url     : https://prove2.me/theorems/dd738781-0e48-457c-8d69-dd583557dbcb
-- title:
--   Eqs. (69)–(73) — cumulative squared error of the recovery learner is $\le cs$
-- statement:
--   There is a constant $c\in\mathbb N$ such that the following holds. Take any source model, any $n,s,t,m$, any program $T$ with $|T|\le s$ (source $\rho=\rho^T$) and any instruments $\mathcal I_1,\dots,\mathcal I_m$. Let $\mu$ be the reference state (uniform mixture over programs of length $\le s$), $\mu_{\le i|h<i}$ its history-conditioned state (Eq. (59)), $\mathcal N_i=\mathrm{Tr}_{R_iX_i}$ and $\mathcal R$ the recovery map of Eq. (26). Then
--
--   $$
--   \sum_{i\in[m]}\ \mathbb E_{x_{<i}\sim D^{\mathcal I,\rho}_{<i}}\Big[\mathrm{TD}\big(\mathcal R_{\mu_{\le i|h<i},\mathcal N_i}(\rho_{<i|h<i}),\,\tau_{\le i|h<i}\big)^2\Big]\ \le\ c\,s .
--   $$
--
--   The left side is the total expected squared error of the learner of §4.2 (step 4 returns $\mathcal R_{\mu_{\le i|h<i},\mathcal N_i}(\rho_{<i|h<i})$). The paper bounds it by $\sum_i\Delta_i=D(\omega^\rho_m\|\omega^\mu_m)\le D(\rho_{\le m}\|\mu_{\le m})\le cs$. Markov's inequality then gives Theorem 4.2 (Eqs. (74)–(76)). The constant does not depend on the source model, $n$, $t$, $m$ or the instruments.
--
--   Differences from the source:
--   - generalization: sources in C_{n,m}[s,t] (Turing-machine model), reference μ^{U,p(s,t)} → every source model, with the reference refState (uniform mixture over programs of length ≤ s); c ∈ ℕ uniform in the model; reason: the paper's model is one source model; the reference is the one of milestone Eq. (58) in this development (paper.md R1–R2)
--   - encoding: E_{x<i}[TD(L(param, h<i, I_i, ρ_{<i|h<i}), τ_{≤i|h<i})²] → Σ_x D^{I,ρ}_{<i}(x)·(½ traceDist(recovery(μ_{≤i|h<i}, Tr_{R_iX_i})(ρ_{<i|h<i}), τ_{≤i|h<i}))²; reason: the learner's output is the recovery map applied to its input (step 4); TD = ½‖·‖₁
--   - encoding: constant c with D in bits → existential c ∈ ℕ; reason: with an existential constant the base of the logarithm does not matter
--   - encoding: registers R_i of n qubits; outcome register written first in M_I → Fin (2^n) per register, register R_i = coordinate i−1; output indexed (past registers) × (next register × outcome); reason: relabelling of the index set; changes no trace, trace distance or relative entropy
--   - encoding: conditional states defined for histories of positive probability → 0⁻¹ = 0 makes them the zero matrix on histories of probability zero; reason: those histories have weight zero in every sum; only undefined cases are affected
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eqs. (69)–(73), p.21; learner: algorithm steps 2–4, p.20

import Mathlib
import Definitions.Def_QIndInf_refState
import Definitions.Def_QIndInf_refCond
import Definitions.Def_QIndInf_successProb
import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

set_option autoImplicit false

namespace QIndInf

open QAlgorithms.CopyMeasurements
open QAlgorithms.Papers.Independent.Dependency50.P21 (recovery)

/-- **Cumulative squared prediction error of the recovery learner** (Eqs. (69)–(73)). There is
a constant `c` such that for every source model `gen`, all `n, s, t, m`, every program `T` with
`|T| ≤ s` (source `ρ = gen n t T`) and all instruments `I₁, …, I_m`,
`∑_{i ∈ [m]} E_{x<i ∼ D^{I,ρ}_{<i}} [ TD(R_{μ_{≤i|h<i}, N_i}(ρ_{<i|h<i}), τ_{≤i|h<i})² ] ≤ c·s`,
where `μ = refState gen n s t` is the reference family, `μ_{≤i|h<i}` its history-conditioned state
(Eq. (59)), `N_i = Tr_{R_i X_i}` and `R_{μ,N}` the recovery map of Eq. (26).

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eqs. (69)–(73), p.21: the learner of step 4 (p.20)
returns `R_{μ_{≤i|h<i}, N_i}(ρ_{<i|h<i})`, and the sum of its expected squared errors over the
rounds is bounded by `∑ Δ_i = D(ω^ρ_m‖ω^μ_m) ≤ D(ρ_{≤m}‖μ_{≤m}) ≤ cs`.

**Formalization Note.**
* `c` is a natural number quantified before the source model; it does not depend on `gen`, `n`,
  `t`, `s`, `m` or the instruments. The paper's `c` measures relative entropy in bits; with an
  existential constant the base does not matter.
* The learner's output is written as the recovery map `P21.recovery` applied to `ρ_{<i|h<i}`
  (step 4 of the algorithm), so no learner type is involved. `TD = ½ · WildeQIT.traceDist`.
* Round `i ∈ [m]` is `j = i − 1 : Fin m`; its past outcomes are weighted by `outcomeProb`
  (Eq. (52)). -/
theorem cumulative_squared_error_le :
    ∃ c : ℕ, ∀ (gen : SourceModel) (n s t m : ℕ) (T : List Bool), T.length ≤ s →
      ∀ (k : Fin m → ℕ) (I : (j : Fin m) → QuantumInstrument (Reg n) (Fin (k j))),
        ∑ j : Fin m, ∑ x : (l : Fin j.val) → Fin (prefK k j l.castSucc),
          outcomeProb (gen n t T).state (pastInstr (prefI I j)) x *
            ((1 / 2 : ℝ) * WildeQIT.traceDist
              (recovery (refCond (refState gen n s t) (prefI I j) x) WildeQIT.partialTraceRight
                (condPast (gen n t T).state (pastInstr (prefI I j)) x))
              (target (gen n t T).state (prefI I j) x)) ^ 2 ≤ (c * s : ℝ) := by sorry

end QIndInf
