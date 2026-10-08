-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_minion_laws
-- name    : PCSPBLPAff.Characterization.minion_laws
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:35.362009+00:00
-- url     : https://prove2.me/theorems/427dc2ff-7141-45bd-bd1a-37358e7e026d
-- title:
--   §5, p. 10 — M_BLP+Aff is a minion: minors of objects are objects, minors compose, the identity minor is trivial
-- statement:
--   Let $\iota,\kappa,\mu$ be finite sets, $\pi:\iota\to\kappa$ and $\sigma:\kappa\to\mu$, and let $(w,r)$ be an object of $\mathcal M_{\mathrm{BLP+Aff}}$ with coordinate set $\iota$: $w\ge0$, $\sum_i w(i)=1$, $\sum_i r(i)=1$, and $w(i)=0\Rightarrow r(i)=0$. With the minor $w_{/\pi}(k)=\sum_{j\in\pi^{-1}(k)}w(j)$ (and likewise for $r$), the following hold:
--
--   1. $(w_{/\pi},r_{/\pi})$ is again an object of $\mathcal M_{\mathrm{BLP+Aff}}$;
--   2. $(w_{/\pi})_{/\sigma}=w_{/\sigma\circ\pi}$ and $(r_{/\pi})_{/\sigma}=r_{/\sigma\circ\pi}$;
--   3. $w_{/\mathrm{id}}=w$ and $r_{/\mathrm{id}}=r$.
--
--   $$\bigl((w,r)_{/\pi}\bigr)_{/\sigma}=(w,r)_{/\sigma\circ\pi},\qquad (w,r)_{/\mathrm{id}}=(w,r).$$
--
--   This is the claim, stated after Definition 6, that $\mathcal M_{\mathrm{BLP+Aff}}$ is indeed a minion (Definition 5). Item 1 is what makes the minion homomorphism condition meaningful.
--
--   **Formalization Note** Coordinate sets are arbitrary finite types rather than only $[L]$; the free structure uses objects indexed by $A$ and by tuples.
-- source:
--   arXiv:1907.04383v3, §5, p. 10, sentence after Definition 6 ("It is easy to check this indeed defines a minion")

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- §5, p. 10: `M_BLP+Aff` is a minion. The minor of an object is an object (in particular
`w(i) = 0 ⟹ r(i) = 0` is preserved), minors compose, `((w, r)_{/π})_{/σ} = (w, r)_{/σ ∘ π}`,
and the minor along the identity is the identity. -/
theorem minion_laws {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]
    (π : ι → κ) (σ : κ → μ) (w : ι → ℚ) (r : ι → ℤ) (h : IsBLPAffObj w r) :
    IsBLPAffObj (minorQ π w) (minorZ π r) ∧
    minorQ σ (minorQ π w) = minorQ (σ ∘ π) w ∧ minorZ σ (minorZ π r) = minorZ (σ ∘ π) r ∧
    minorQ id w = w ∧ minorZ id r = r := by sorry

end PCSPBLPAff.Characterization
