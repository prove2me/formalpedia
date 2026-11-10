-- Prove2me | Theorems.Thm_PRUMicrocrypt_lemma_H_1
-- name    : PRUMicrocrypt.lemma_H_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:41.371185+00:00
-- url     : https://prove2.me/theorems/0c97e089-9085-441f-aeda-d9cec0836874
-- title:
--   Lemma H.1 — error propagation through contractions
-- statement:
--   Let $\mathcal K,\mathcal H$ be complex Hilbert spaces, $T:\mathcal K\to\mathcal H$ and $M_1,\dots,M_t$ contractions, $U_1,\dots,U_t$ unitaries on $\mathcal H$, and suppose $\|T^\dagger U_iT-M_i\|\le\eta$ for all $i$. From a unit vector $|K_0\rangle$ and a vector $|\Phi_0\rangle$ define $|K_i\rangle=M_i|K_{i-1}\rangle$ and $|\Phi_i\rangle=U_i|\Phi_{i-1}\rangle$. If $\||\Phi_0\rangle-T|K_0\rangle\|\le d_0$, then
--
--   $$\||\Phi_t\rangle-T|K_t\rangle\|\le d_0+\sqrt{t\,(1-\||K_t\rangle\|^2)+2t^2\eta}.$$
--
--   The lemma turns per-step compression errors and the total norm lost by the compressed evolution into a bound on the full-state error. It is used to prove Proposition 4.6 and hence Theorem 4.1.
--
--   Differences from the source:
--   - generalization: from a unit vector |K_0⟩ and |Φ_0⟩ → |K_0⟩ a unit vector, |Φ_0⟩ an arbitrary vector; reason: if the intended reading is that both are unit vectors, the Lean statement contains that case; the proof never uses ‖Φ_0‖
--   - encoding: contractions, unitaries M_i, U_i for i = 1, …, t → bounded operators of norm at most 1, unitary operators, indexed M (i − 1), U (i − 1); reason: index shift only
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma H.1, p.81

import Mathlib
import Definitions.Def_PRUMicrocrypt_QueryAlg

set_option autoImplicit false

namespace PRUMicrocrypt

/-- **Lemma H.1 (Error propagation through contractions).** "Let T : 𝒦 → ℋ and M_1, …, M_t be
contractions, let U_1, …, U_t be unitaries, and suppose ‖T†U_iT − M_i‖ ≤ η. From a unit vector |K_0⟩
and |Φ_0⟩, define |K_i⟩ = M_i|K_{i−1}⟩ and |Φ_i⟩ = U_i|Φ_{i−1}⟩. If ‖|Φ_0⟩ − T|K_0⟩‖ ≤ d_0, then
‖|Φ_t⟩ − T|K_t⟩‖ ≤ d_0 + √(t(1 − ‖|K_t⟩‖²) + 2t²η). (H.2) The spaces may include arbitrary
Hilbert-space references, with all maps extended by identity on untouched registers."
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma H.1, p.81.

**Formalization Note.** `𝒦, ℋ` are arbitrary complex Hilbert spaces; operators are bounded
(contraction: operator norm `≤ 1`). The paper's `M_i, U_i` (`i = 1, …, t`) are `M (i − 1)`,
`U (i − 1)`, and `trajectory` builds `|K_i⟩`, `|Φ_i⟩`. "Unit" is read on `|K_0⟩` only; `|Φ_0⟩` is
arbitrary. -/
theorem lemma_H_1 {𝒦 ℋ : Type*} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (t : ℕ) (T : 𝒦 →L[ℂ] ℋ) (hT : ‖T‖ ≤ 1)
    (M : ℕ → 𝒦 →L[ℂ] 𝒦) (hM : ∀ i < t, ‖M i‖ ≤ 1)
    (U : ℕ → ℋ →L[ℂ] ℋ) (hU : ∀ i < t, U i ∈ unitary (ℋ →L[ℂ] ℋ))
    (η : ℝ) (hη : ∀ i < t, ‖ContinuousLinearMap.adjoint T ∘L U i ∘L T - M i‖ ≤ η)
    (K₀ : 𝒦) (hK₀ : ‖K₀‖ = 1) (Φ₀ : ℋ) (d₀ : ℝ) (hd₀ : ‖Φ₀ - T K₀‖ ≤ d₀) :
    ‖trajectory (fun i Φ => U i Φ) Φ₀ t - T (trajectory (fun i K => M i K) K₀ t)‖ ≤
      d₀ + Real.sqrt ((t : ℝ) * (1 - ‖trajectory (fun i K => M i K) K₀ t‖ ^ 2) +
        2 * (t : ℝ) ^ 2 * η) := by sorry

end PRUMicrocrypt
