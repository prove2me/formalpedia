-- Prove2me | Theorems.Thm_SubsetConvFPRAS_proposition_5_11
-- name    : SubsetConvFPRAS.proposition_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:44.769458+00:00
-- url     : https://prove2.me/theorems/3e3b3d05-ae65-4f49-87a6-ccddb9965651
-- title:
--   Proposition 5.11 — the induced chain is reversible and keeps the spectral gap
-- statement:
--   Let $r$ be the rates of an irreducible chain on a finite set $\Omega$, reversible with respect to a positive law $\pi$, with spectral gap at least $\gamma>0$, and let $\emptyset\ne B\subseteq\Omega$. Then:
--
--   1. the hitting law $h(u,y)=\Pr[X_{\tau_B}=y\mid X_0=u]$ is the unique solution of its first-step equations ($h(\cdot,y)=\mathbf 1_y$ on $B$, $L_rh(\cdot,y)=0$ off $B$);
--   2. the induced chain on $B$, with rates $r_B(x,y)=r(x,y)+\sum_{u\notin B}r(x,u)h(u,y)$, is reversible with respect to $\pi_B(x)=\pi(x)/\pi(B)$, and for every $f:B\to\mathbb R$
--   $$\gamma\operatorname{Var}_{\pi_B}[f]\le\mathcal E_{r_B}(f,f).$$
--
--   This is how the Poincaré bound of Corollary 5.7 passes from the independent-set pair law to the bases pair law in Lemma 5.5.
--
--   Differences from the source:
--   - generalization: the hitting probability Pr[X_{τ_B} = y | X₀ = u] of the process → any solution of the first-step linear system, together with the added clause that this system has exactly one solution; reason: the clause makes the defined object the page's hitting law, so the conclusion is about the page's induced chain; with it the statement implies the source's
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Definition 5.10 and Proposition 5.11, p.23 (citing Levin–Peres, Theorem 13.16; proof p.40)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_ReversibleChain

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Definition 5.10 and Proposition 5.11, p.23. For an
irreducible reversible chain with spectral gap at least `γ > 0` and `∅ ≠ B ⊆ Ω`, the hitting law on `B` exists
and is unique, and the induced chain is reversible with respect to `π_B` with
`γ Var_{π_B}[f] ≤ E_{r_B}(f,f)`.

**Formalization Note.** The first clause says that `IsHittingLaw` determines the object Definition 5.10
constructs, so the second clause is not vacuous. -/
theorem proposition_5_11 {Ω : Type} [Fintype Ω] (π : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hr : IsReversibleChain π r) (hi : IsIrreducible r) (γ : ℝ) (hγ : 0 < γ)
    (hgap : HasPoincare π r γ) (B : Finset Ω) (hB : B.Nonempty) :
    (∃ h : Ω → Ω → ℝ, IsHittingLaw r B h ∧
      ∀ h' : Ω → Ω → ℝ, IsHittingLaw r B h' → ∀ u, ∀ y ∈ B, h' u y = h u y) ∧
    ∀ h : Ω → Ω → ℝ, IsHittingLaw r B h →
      IsReversibleChain (conditionedLaw π B) (inducedRate r B h) ∧
        HasPoincare (conditionedLaw π B) (inducedRate r B h) γ := by sorry

end SubsetConvFPRAS
