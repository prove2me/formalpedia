-- Prove2me | Theorems.Thm_TeschlQM_Spectral_spectralIntegral_add_mul
-- name    : TeschlQM.Spectral.spectralIntegral_add_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:29:38.727756+00:00
-- url     : https://prove2.me/theorems/07e91749-e945-4056-af6b-b739c5afa002
-- title:
--   Lemma 3.5 — sums and products of spectral integrals
-- statement:
--   Let $P$ be a projection-valued measure on a complex Hilbert space $\mathfrak H$, let $f, g$ be Borel functions and $\alpha, \beta \in \mathbb{C}$. Then
--   $$\alpha P(f) + \beta P(g) \subseteq P(\alpha f + \beta g), \qquad \mathfrak D(\alpha P(f) + \beta P(g)) = \mathfrak D_{|f|+|g|} \qquad (3.38)$$
--   and
--   $$P(f)P(g) \subseteq P(fg), \qquad \mathfrak D(P(f)P(g)) = \mathfrak D_g \cap \mathfrak D_{fg} \qquad (3.39).$$
--   Here $\alpha P(f) + \beta P(g)$ has domain $\mathfrak D(P(f)) \cap \mathfrak D(P(g))$, $P(f)P(g)$ has domain $\{\psi \in \mathfrak D(P(g)) \mid P(g)\psi \in \mathfrak D(P(f))\}$, and $S \subseteq T$ means that $T$ extends $S$.
--
--   **Formalization Note.** Sum and scalar multiple are Mathlib's `LinearPMap` operations (the domain of a sum is the intersection of domains, and $\alpha T$ has the domain of $T$ also for $\alpha = 0$, as for operators in the book), and $\subseteq$ is the order `≤` on `LinearPMap`s. Mathlib has no composition of arbitrary partially defined operators, so (3.39) is written out: a vector lies in the natural domain of $P(f)P(g)$ iff it lies in $\mathfrak D_g \cap \mathfrak D_{fg}$, and for every such vector $\psi$ one has $\psi \in \mathfrak D(P(fg))$ and $P(f)(P(g)\psi) = P(fg)\psi$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 94, Lemma 3.5

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 94, Lemma 3.5. For Borel functions `f, g` and `α, β ∈ ℂ`:
(3.38) `αP(f) + βP(g) ⊆ P(αf + βg)` with `𝔇(αP(f) + βP(g)) = 𝔇_{|f|+|g|}`, and
(3.39) `P(f)P(g) ⊆ P(fg)` with `𝔇(P(f)P(g)) = 𝔇_g ∩ 𝔇_{fg}`, where `P(f)P(g)` has the natural
domain `{ψ ∈ 𝔇(P(g)) | P(g)ψ ∈ 𝔇(P(f))}`. -/
theorem spectralIntegral_add_mul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) (α β : ℂ) :
    α • spectralIntegral P f + β • spectralIntegral P g ≤ spectralIntegral P (α • f + β • g) ∧
    ((α • spectralIntegral P f + β • spectralIntegral P g).domain : Set H) =
      spectralDomain P (fun x => ((‖f x‖ + ‖g x‖ : ℝ) : ℂ)) ∧
    (∀ ψ : H, (∃ hψ : ψ ∈ (spectralIntegral P g).domain,
        spectralIntegral P g ⟨ψ, hψ⟩ ∈ (spectralIntegral P f).domain) ↔
      ψ ∈ spectralDomain P g ∩ spectralDomain P (f * g)) ∧
    (∀ (ψ : (spectralIntegral P g).domain)
        (h : spectralIntegral P g ψ ∈ (spectralIntegral P f).domain),
      ∃ h' : (ψ : H) ∈ (spectralIntegral P (f * g)).domain,
        spectralIntegral P f ⟨spectralIntegral P g ψ, h⟩ =
          spectralIntegral P (f * g) ⟨ψ, h'⟩) := by sorry

end TeschlQM.Spectral
