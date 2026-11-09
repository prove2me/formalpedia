-- Prove2me | Theorems.Thm_SelectiveDPT_lemma_3_3
-- name    : SelectiveDPT.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:04.474714+00:00
-- url     : https://prove2.me/theorems/fab0e8b2-b140-480f-9d23-3c672a5e81cc
-- title:
--   Lemma 3.3 — $\|\Pi_{f^{-1}(y)}\Pi_{\Gamma,\le\lambda}\|^2 \le 1/(3-\lambda)$ for $\Gamma = 2I-\Gamma^\pm$
-- statement:
--   Let $f : D \to Y$, let $\mu$ be a distribution on $D$, let $\Gamma^\pm$ be a witness to Proposition 2.5 for computing $f$ under $\mu$, and let $1 < \lambda < 3$. Let $\Gamma = 2I - \Gamma^\pm$. Then for every $y \in Y$,
--   $$\big\|\Pi_{f^{-1}(y)}\,\Pi_{\Gamma,\le\lambda}\big\|^2 \le \frac{1}{3-\lambda},$$
--   with $\|\cdot\|$ the spectral norm.
--
--   This is the $(\lambda,\eta)$ condition of the relational multiplicative adversary method for the matrix $2I - \Gamma^\pm$.
--
--   Differences from the source: none.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Lemma 3.3, p.20

import Mathlib
import Definitions.Def_SelectiveDPT_IsNegAdvWitness
import Definitions.Def_SelectiveDPT_projLe
import Definitions.Def_SelectiveDPT_rangeProj

namespace SelectiveDPT

open QAlgorithms

/-- Lemma 3.3 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.20: let `Γ±` be any witness to
Proposition 2.5 for computing `f` under the distribution `D` and let `1 < λ < 3`. Let
`Γ = 2I − Γ±`. Then `∀ y ∈ Y, ‖Π_{f⁻¹(y)} Π_{Γ,≤λ}‖² ≤ 1/(3 − λ)`.

**Formalization Note.** `‖·‖` is the spectral norm; `Π_{f⁻¹(y)}` is `rangeProj` of the graph
of `f`. -/
theorem lemma_3_3 {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (μ : (ι → ZMod d) → ℝ) (hμ : IsDistOn μ D)
    (f : (ι → ZMod d) → Y) (Γpm : Matrix D D ℂ) (hΓ : IsNegAdvWitness μ D f Γpm) (lam : ℝ)
    (hlam₁ : 1 < lam) (hlam₃ : lam < 3) :
    ∀ y : Y, specNorm (rangeProj D (fun x y => f x = y) y *
        projLe ((2 : ℂ) • (1 : Matrix D D ℂ) - Γpm) lam) ^ 2 ≤ 1 / (3 - lam) := by sorry

end SelectiveDPT
