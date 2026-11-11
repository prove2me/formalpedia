-- Prove2me | Theorems.Thm_QIndInf_measured_relEntropy_increment
-- name    : QIndInf.measured_relEntropy_increment
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:30:07.748894+00:00
-- url     : https://prove2.me/theorems/82a52985-dced-42c1-8695-68d3b3035df1
-- title:
--   Eqs. (61)–(63) — relative-entropy increment of one round
-- statement:
--   Let $\rho$ and $\mu$ be quantum sources on $n$-qubit registers and suppose that $\rho_{R_1\dots R_i}\le\lambda\,\mu_{R_1\dots R_i}$ for some real $\lambda>0$. Let $\mathcal I_1,\dots,\mathcal I_i$ be instruments and let
--
--   $$
--   \omega^\rho_j=(\mathcal M_{\mathcal I_1}\otimes\cdots\otimes\mathcal M_{\mathcal I_j})\rho_{\le j},\qquad \omega^\mu_j=(\mathcal M_{\mathcal I_1}\otimes\cdots\otimes\mathcal M_{\mathcal I_j})\mu_{\le j}\qquad\text{(Eq. (61))}.
--   $$
--
--   Then the increment $\Delta_i=D(\omega^\rho_i\|\omega^\mu_i)-D(\omega^\rho_{i-1}\|\omega^\mu_{i-1})$ (Eq. (62)) equals
--
--   $$
--   \Delta_i=\sum_{x_1,\dots,x_{i-1}}D^{\mathcal I,\rho}_{<i}(x)\Big[D\big(\tau_{\le i|h<i}\,\big\|\,\mu_{\le i|h<i}\big)-D\big(\rho_{<i|h<i}\,\big\|\,\mu_{<i|h<i}\big)\Big]\qquad\text{(Eq. (63))},
--   $$
--
--   with $\mu_{\le i|h<i}$ and $\mu_{<i|h<i}$ from Eqs. (59)–(60). Summed over $i$, the increments telescope to $D(\omega^\rho_m\|\omega^\mu_m)$.
--
--   **Formalization Note** The domination hypothesis makes every relative entropy finite, so no $\infty-\infty$ occurs; in the paper it holds by Eq. (58), which is in force throughout the proof.
--
--   Differences from the source:
--   - generalization: ρ ∈ C_{n,m}[s,t] and μ the universal density matrix of Eq. (58) → any two quantum sources ρ, μ with ρ_{≤i} ≤ λ μ_{≤i} for some λ > 0; reason: the paper's pair satisfies the hypothesis with λ = 2^{cs} by Eq. (58), so the paper's identity is the instance
--   - encoding: relative entropy D in bits (log = log₂, p.14) → published P21.relativeEntropy in nats (EReal, +∞ off support); reason: the statement is homogeneous in the base of the logarithm: both sides scale by the same factor 1/ln 2
--   - encoding: registers R_i of n qubits; outcome register written first in M_I → Fin (2^n) per register, register R_i = coordinate i−1; output indexed (past registers) × (next register × outcome); reason: relabelling of the index set; changes no trace, trace distance or relative entropy
--   - encoding: conditional states defined for histories of positive probability → 0⁻¹ = 0 makes them the zero matrix on histories of probability zero; reason: those histories have weight zero in every sum; only undefined cases are affected
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eqs. (61)–(63), p.20, with Eqs. (59)–(60)

import Mathlib
import Definitions.Def_QIndInf_refCond
import Definitions.Def_QIndInf_measAll
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

set_option autoImplicit false

open scoped ComplexOrder

namespace QIndInf

open QAlgorithms.CopyMeasurements
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Relative-entropy increment of one round** (Eqs. (61)–(63)). Let `ρ` and `μ` be quantum
sources with `μ_{≤i} ≥ λ⁻¹ ρ_{≤i}` for some `λ > 0`, and let `ω^ρ_j`, `ω^μ_j` be the states of
the first `j` registers after measuring each with its instrument, outcomes recorded (Eq. (61)).
Then for round `i = j + 1`
`Δ_i = D(ω^ρ_i‖ω^μ_i) − D(ω^ρ_{i−1}‖ω^μ_{i−1})
     = ∑_{x₁,…,x_{i−1}} D^{I,ρ}_{<i}(x) [D(τ_{≤i|h<i}‖μ_{≤i|h<i}) − D(ρ_{<i|h<i}‖μ_{<i|h<i})]`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eqs. (61)–(63), p.20, with `μ_{≤i|h<i}` from Eq. (59)
and `μ_{<i|h<i}` from Eq. (60).

**Formalization Note.**
* `D` is the published `P21.relativeEntropy` (natural logarithm, `EReal`-valued, `+∞` without
  support inclusion). The identity is homogeneous in the base of the logarithm, so it is the
  paper's identity in bits up to the common factor `ln 2`.
* The domination hypothesis `(λ μ_{≤i} − ρ_{≤i}) ⪰ 0` makes every relative entropy in the identity
  finite, so no `∞ − ∞` occurs; in the paper it holds by Eq. (58), which is in force throughout
  the proof.
* Round `i` has `j = i − 1` past registers; `I` lists `I₁, …, I_i`. -/
theorem measured_relEntropy_increment {n j : ℕ} (ρ μ : QuantumProcess n)
    {k : Fin (j + 1) → ℕ} (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (lam : ℝ) (hlam : 0 < lam)
    (hdom : ((lam : ℂ) • μ.state (j + 1) - ρ.state (j + 1)).PosSemidef) :
    relativeEntropy (measAll I (ρ.state (j + 1))) (measAll I (μ.state (j + 1))) -
        relativeEntropy (measAll (pastInstr I) (ρ.state j)) (measAll (pastInstr I) (μ.state j)) =
      ∑ x : (l : Fin j) → Fin (k l.castSucc),
        ((outcomeProb ρ.state (pastInstr I) x : ℝ) : EReal) *
          (relativeEntropy (target ρ.state I x) (refCond μ.state I x) -
            relativeEntropy (condPast ρ.state (pastInstr I) x) (refPast μ.state I x)) := by sorry

end QIndInf
