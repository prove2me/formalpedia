-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_28
-- name    : RamseyDisambig.Spherical.Supplement.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:27:57.845923+00:00
-- url     : https://prove2.me/theorems/c3c76191-bfab-418c-a12a-5448c849e731
-- title:
--   Lemma 28 — Amalgamation Lemma for profiles
-- statement:
--   Let $\alpha,\beta,\gamma$ be profiles, let $\varphi_\alpha$ be a copy of $\alpha$ in $\beta$ and let $\psi_\alpha$ be a copy of $\alpha$ in $\gamma$ (so that $\beta$ and $\gamma$ both refine $\alpha$). Then there are a profile $\delta$, a copy $\varphi_\beta$ of $\beta$ in $\delta$ and a copy $\psi_\gamma$ of $\gamma$ in $\delta$ (so that $\delta$ refines both $\beta$ and $\gamma$) such that
--   $$\varphi_\alpha\circ\varphi_\beta=\psi_\alpha\circ\psi_\gamma .$$
--
--   The lemma completes a span of copies to a commuting square, and is the amalgamation step in the proof of Lemma 31.
--
--   **Formalization Note** Copies are maps between `Fin`-indexed part sets; the commuting square is an equality of functions $[p(\delta)]\to[p(\alpha)]$.
--
--   Differences from the source:
--   - encoding: profiles, rigid surjections, α-partitions, copies, coarsening → Profile structure (Fin-indexed positive rationals summing to 1), rigid surjection = surjective with strictly increasing fibre minima (Finset.min in WithTop), α-partition = rigid surjection with fibre sizes |π⁻¹(j)|/N = α_j, coarsening σ = ψ ∘ π for some map ψ; reason: 0-based Fin indices; the same objects as on p. 27
--   - encoding: 'β and γ both refine α' and 'δ refines both β and γ' → witnessed by the given copies ϕα, ψα and the constructed copies ϕβ, ψγ; no separate refinement hypothesis; reason: refinement is by definition the existence of a copy (p. 27), so separate hypotheses would be redundant
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 28, p. 28 (proof pp. 28–29) (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_DualRamsey

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Lemma 28 (Amalgamation Lemma), p. 28 (proof pp. 28–29). `β` and `γ` refining `α` is
witnessed by the given copies `ϕα`, `ψα`; `δ` refining `β` and `γ` by the constructed copies. -/
theorem lemma_28 (α β γ : Profile) (ϕα : Fin β.len → Fin α.len) (ψα : Fin γ.len → Fin α.len)
    (hϕα : IsProfileCopy α β ϕα) (hψα : IsProfileCopy α γ ψα) :
    ∃ (δ : Profile) (ϕβ : Fin δ.len → Fin β.len) (ψγ : Fin δ.len → Fin γ.len),
      IsProfileCopy β δ ϕβ ∧ IsProfileCopy γ δ ψγ ∧ ϕα ∘ ϕβ = ψα ∘ ψγ := by sorry

end RamseyDisambig.Spherical.Supplement
