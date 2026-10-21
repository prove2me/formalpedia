-- Prove2me | Theorems.Thm_SetOptLattice_Existence_remark_3_3
-- name    : SetOptLattice.Existence.remark_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:48.850448+00:00
-- url     : https://prove2.me/theorems/909af839-5054-41f1-a5fb-f00fb7df8a92
-- title:
--   Remark 3.3, p. 14 — Min(f,ε,Ψ) monotone in ε, Min(f,ε,Ψ) ⊆ Min(f,ε+,Ψ), (3.1) and (3.2)
-- statement:
--   Let $(Z,\preceq)$ be a preordered set, $\Psi$ a family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$, $X$ a set and $f\colon X\to\mathcal P(Z,\Psi)$. Write $\operatorname{Min}(f,\varepsilon,\Psi)$ and $\operatorname{Min}(f,\varepsilon+,\Psi)$ for the sets of $(\varepsilon,\Psi)$- and $(\varepsilon+,\Psi)$-minimizers of $f$ (Definition 3.2). Then:
--
--   1. for $0\le\varepsilon_1\le\varepsilon_2$, $\operatorname{Min}(f,\varepsilon_1,\Psi)\subseteq\operatorname{Min}(f,\varepsilon_2,\Psi)$ and $\operatorname{Min}(f,\varepsilon_1+,\Psi)\subseteq\operatorname{Min}(f,\varepsilon_2+,\Psi)$;
--   2. $\operatorname{Min}(f,\varepsilon,\Psi)\subseteq\operatorname{Min}(f,\varepsilon+,\Psi)$ for all $\varepsilon\ge 0$;
--   3. for all $\varepsilon\ge0$,
--   $$\operatorname{Min}(f,\varepsilon+,\Psi)=\bigcap_{\delta>0}\operatorname{Min}(f,\varepsilon+\delta,\Psi); \tag{3.1}$$
--   4. $$\operatorname{Min}(f,0+,\Psi)=\bigcap_{\varepsilon>0}\operatorname{Min}(f,\varepsilon,\Psi)=\bigcap_{\varepsilon>0}\operatorname{Min}(f,\varepsilon+,\Psi). \tag{3.2}$$
--
--   Identity (3.2) presents $\operatorname{Min}(f,0+,\Psi)$ as a decreasing intersection, which is what the existence theorem of §4 exploits.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 14, sentence before Remark 3.3 and Remark 3.3 (1)–(3), (3.1), (3.2)

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Remark 3.3, p. 14, with the monotonicity in `ε` stated just before it. -/
theorem remark_3_3 {X Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x)) :
    (∀ ε₁ ε₂ : ℝ, 0 ≤ ε₁ → ε₁ ≤ ε₂ →
        MinSet Ψ f ε₁ ⊆ MinSet Ψ f ε₂ ∧ MinPlusSet Ψ f ε₁ ⊆ MinPlusSet Ψ f ε₂) ∧
      (∀ ε : ℝ, 0 ≤ ε → MinSet Ψ f ε ⊆ MinPlusSet Ψ f ε) ∧
      (∀ ε : ℝ, 0 ≤ ε → MinPlusSet Ψ f ε = ⋂ (δ : ℝ) (_ : 0 < δ), MinSet Ψ f (ε + δ)) ∧
      MinPlusSet Ψ f 0 = ⋂ (ε : ℝ) (_ : 0 < ε), MinSet Ψ f ε ∧
      MinPlusSet Ψ f 0 = ⋂ (ε : ℝ) (_ : 0 < ε), MinPlusSet Ψ f ε := by sorry

end SetOptLattice.Existence
