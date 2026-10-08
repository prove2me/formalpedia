-- Prove2me | Theorems.Thm_RegMT_Regress_lemma_A_3
-- name    : RegMT.Regress.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:34.470982+00:00
-- url     : https://prove2.me/theorems/e8845076-3bff-4979-9bad-f1aed533d3ec
-- title:
--   Lemma A.3, p. 29 — sup_ζ L(⟨β, ζ⟩) − γ‖ζ − ζ̂‖ is L(⟨β, ζ̂⟩) if lip(L)‖β‖_* ≤ γ and +∞ otherwise
-- statement:
--   Let $L:\mathbb R\to\mathbb R$ be a nonnegative, convex and Lipschitz continuous loss function, and let $\mathrm{lip}(L)=\sup_{z\neq z'}|L(z)-L(z')|/|z-z'|$ be its Lipschitz modulus. Let $\mathbb R^d$ carry an arbitrary norm $\|\cdot\|$ with dual norm $\|\cdot\|_*$, let $\beta,\hat\zeta\in\mathbb R^d$, and let $\gamma>0$. Then
--
--   $$
--   \sup_{\zeta\in\mathbb R^d}\ L(\langle\beta,\zeta\rangle)-\gamma\|\zeta-\hat\zeta\|
--   \;=\;
--   \begin{cases}
--   L(\langle\beta,\hat\zeta\rangle) & \text{if } \mathrm{lip}(L)\,\|\beta\|_*\le\gamma,\\
--   +\infty & \text{otherwise.}
--   \end{cases}
--   $$
--
--   The supremum is taken in the extended reals. The lemma evaluates the inner suprema produced by the robust reformulation (Lemma A.1) when the integrand is a convex Lipschitz loss of a linear function. Every summand then either equals the nominal loss at the sample or is $+\infty$, and this produces the constraint $\mathrm{lip}(L)\|(w,-1)\|_*\le\lambda$ in the proof of Theorem 3.1(ii).
--
--   **Formalization Note.** $\mathbb R^d$ with an arbitrary norm is a finite-dimensional real normed space $V$. The vector $\beta$ acts as a continuous linear functional on $V$, and $\|\beta\|_*$ is its operator norm. $\mathrm{lip}(L)$ is the published `lipschitzModulus`, valued in $[0,\infty]$, and the condition $\mathrm{lip}(L)\|\beta\|_*\le\gamma$ is compared in $[0,\infty]$. Because $L$ is Lipschitz, $\mathrm{lip}(L)$ is finite and the comparison is the real one. The hypothesis $\gamma>0$ is printed in the lemma.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 29, Lemma A.3; proof pp. 29–30

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

namespace RegMT.Regress

/-- Lemma A.3, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, *Regularization via Mass
Transportation*, arXiv:1710.10016v3, p. 29. Let `L : ℝ → ℝ` be convex and Lipschitz continuous,
`V` a finite-dimensional real normed space (the paper's `ℝ^d` with an arbitrary norm), `β` a
continuous linear functional on `V` (the paper's `β ∈ ℝ^d` acting by `⟨β, ·⟩`; its operator norm
is the dual norm `‖β‖_*`), `ζhat ∈ V` and `γ > 0`. Then, in the extended reals,
`sup_ζ L(⟨β, ζ⟩) − γ‖ζ − ζhat‖ = L(⟨β, ζhat⟩)` if `lip(L)‖β‖_* ≤ γ`, and `+∞` otherwise,
where `lip(L)` is the Lipschitz modulus of `L` (§1.1, p. 4), valued in `ℝ≥0∞`.
The loss is nonnegative as in §2.1 (p. 5). -/
theorem lemma_A_3 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (h_nonneg : ∀ z, 0 ≤ L z)
    (hLip : ∃ K, LipschitzWith K L)
    (β : V →L[ℝ] ℝ) (ζhat : V) (γ : ℝ) (hγ : 0 < γ) :
    (⨆ ζ : V, ((L (β ζ) - γ * ‖ζ - ζhat‖ : ℝ) : EReal)) =
      if WassersteinDRO.Duality.lipschitzModulus L * ENNReal.ofReal ‖β‖ ≤ ENNReal.ofReal γ then
        ((L (β ζhat) : ℝ) : EReal)
      else ⊤ := by sorry

end RegMT.Regress
