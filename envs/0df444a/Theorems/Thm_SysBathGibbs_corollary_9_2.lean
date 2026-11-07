-- Prove2me | Theorems.Thm_SysBathGibbs_corollary_9_2
-- name    : SysBathGibbs.corollary_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:43.74647+00:00
-- url     : https://prove2.me/theorems/c40661ab-a2c7-4975-81a2-d5eb244c928f
-- title:
--   Corollary 9.2 — Rapid mixing: $m_{\mathrm{mix}}(\varepsilon)=O\big(\tfrac n\varepsilon(\log^4(en)+\log\tfrac1\varepsilon)\big)$ and $\tilde O(n/\varepsilon)$ evolution time
-- statement:
--   Fix $\beta>0$, $q\ge1$ and $\sigma=\beta/2$. There is $c_0>0$ such that for every $c\in(0,c_0]$ there are $C_{\mathrm{mix}},C_T>0$ with the following property. For every $n\ge1$, every nearest-neighbor chain $H_n=\sum_xh_x$ as in (1.2), every $0<\varepsilon\le1/2$ and every real $\alpha$ with
--   $$
--   \alpha^2=\frac{c\varepsilon}{n},\qquad T_0=\max\Big\{1,\ 2\sigma\sqrt{2\log\frac1{\alpha^2\sigma}}\Big\},
--   $$
--   let $\Phi$ be the averaged system-bath channel (1.3) and $S=\{m\in\mathbb N_0:\ \|\Phi^m(\rho_0)-\rho_\beta\|_1\le\varepsilon\text{ for every state }\rho_0\}$. Then $S$ is nonempty, its least element $m_{\mathrm{mix}}(\varepsilon;\rho_\beta)=\min S$ satisfies
--   $$
--   m_{\mathrm{mix}}(\varepsilon;\rho_\beta)\le C_{\mathrm{mix}}\frac n\varepsilon\Big(\log^4(en)+\log\frac1\varepsilon\Big),
--   $$
--   and the expected total Hamiltonian evolution time $T_{\mathrm{total}}=2m\,\mathbb E[T]$ of $m=m_{\mathrm{mix}}(\varepsilon;\rho_\beta)$ rounds satisfies
--   $$
--   T_{\mathrm{total}}\le C_T\frac n\varepsilon\Big(\log^4(en)+\log\frac1\varepsilon\Big)\sqrt{\log\frac{en}\varepsilon}.
--   $$
--
--   This is the end-to-end guarantee of the paper: from any initial state, the parallel system-bath algorithm prepares the Gibbs state of any one-dimensional nearest-neighbor Hamiltonian at any fixed temperature to trace error $\varepsilon$ in expected Hamiltonian evolution time $\tilde O(n/\varepsilon)$, uniformly in the Hamiltonian. The statement assumes nothing beyond (1.2).
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - reading: "c > 0 is a sufficiently small constant" → ∃ c0 > 0, ∀ c ∈ (0, c0]; reason: every condition the proof places on c is an upper bound (pp.74–75); the stronger reading is taken
--   - reading: "C_mix > 0 is independent of n and ε"; T_total = O_{β,q}(…) → C_mix, C_T chosen after β, q, c and before n, the chain, ε, α; reason: §2.1: constants depend on β, q only; the proof uses only (1.2), so they do not depend on the chain
--   - encoding: m_mix = min{…}, infinite when the set is empty (p.13) → the set S is nonempty and sInf S ≤ the bound; reason: on ℕ, sInf ∅ = 0, so nonemptiness is stated separately
--   - encoding: sup_{ρ0 state} ‖Φ^m(ρ0) − ρβ‖₁ ≤ ε → ∀ density operators ρ0, ‖Φ^m(ρ0) − ρβ‖₁ ≤ ε; reason: equivalent
--   - generalization: the choice α² = cε/n → every real α with α² = cε/n; reason: the paper fixes only α²; both roots are covered, which contains the positive root
--   - encoding: T_total = E[Σ 2T_j] = 2mE[T] = 10mT0 (1.9) → 2·m·∫ t dμ_{T0}(t); reason: (1.9) before its last equality
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Corollary 9.2 (eqs. (9.5)–(9.6)); informal version Theorem 1.1, p.6, p.73

import Definitions.Def_SysBathGibbs_Algorithm
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Corollary 9.2 (Rapid mixing and preparation complexity)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.73.
For `0 < ε ≤ 1/2` choose `α² = cε/n`, `T₀ = max{1, 2σ√(2 log(1/(α²σ)))}`, (9.5), with `c > 0` a
sufficiently small constant. Then `m_mix(ε; ρ_β) := min{m ∈ ℕ₀ : sup_{ρ₀ state} ‖Φ^m(ρ₀) - ρ_β‖₁ ≤ ε} ≤
C_mix (n/ε)(log⁴(en) + log(1/ε))`, (9.6), with `C_mix > 0` independent of `n` and `ε`. For
`m = m_mix(ε; ρ_β)` the expected total Hamiltonian evolution time satisfies
`T_total = O_{β,q}((n/ε)(log⁴(en) + log(1/ε)) √(log(en/ε)))`.

**Formalization Note.** `σ = β/2`. "Sufficiently small" is read as every `c ≤ c₀`; `C_mix` and `C_T` may
depend on `c`, and on nothing else but `β, q`. `S` is the set of round counts that reach accuracy `ε`
from every state; a minimum exists only if `S` is nonempty, so nonemptiness is the first clause and
`sInf` on `ℕ` is then its minimum. The theorem has no hypothesis beyond (1.2), and in particular does not
assume the results of [BC26], [CD26], [PGPH23] or [NS06]. -/
theorem corollary_9_2 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ c₀ : ℝ, 0 < c₀ ∧
        ∀ c : ℝ, 0 < c → c ≤ c₀ →
          ∃ Cmix CT : ℝ, 0 < Cmix ∧ 0 < CT ∧
            ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
              ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ α : ℝ, α ^ 2 = c * ε / n →
                let S : Set ℕ :=
                  {m | ∀ ρ₀ : SysMat n q, WildeQIT.IsDensityOperator ρ₀ →
                    WildeQIT.traceNorm
                      ((Phi β h α (T0Choice β α))^[m] ρ₀ - gibbs β (chainHam h)) ≤ ε};
                S.Nonempty ∧
                ((sInf S : ℕ) : ℝ) ≤
                  Cmix * (n / ε) * (Real.log (Real.exp 1 * n) ^ 4 + Real.log (1 / ε)) ∧
                Ttotal (T0Choice β α) (sInf S) ≤
                  CT * (n / ε) * (Real.log (Real.exp 1 * n) ^ 4 + Real.log (1 / ε)) *
                    Real.sqrt (Real.log (Real.exp 1 * n / ε)) := by sorry

end SysBathGibbs
