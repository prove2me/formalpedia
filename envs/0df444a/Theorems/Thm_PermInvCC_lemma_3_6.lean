-- Prove2me | Theorems.Thm_PermInvCC_lemma_3_6
-- name    : PermInvCC.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:01.527652+00:00
-- url     : https://prove2.me/theorems/0cbeb025-841b-45a6-8b59-da331c2cf01b
-- title:
--   Lemma 3.6 — decoding from Hellinger estimates
-- statement:
--   Let $f$ be a permutation-invariant partial function on $[q]^n\times[q]^n$ whose promised inputs all have histograms $\rho,\sigma$ (known margins) and which takes both values $+1$ and $-1$; let $h:=h_f$. Let $T$ be a promised type with label $b_T$. Suppose probability distributions $\hat J^E$, one for each $E\in\mathcal E$, satisfy $\max_EH(J^E_T,\hat J^E)\le\varepsilon$, and set $D(U):=\max_EH(J^E_U,\hat J^E)$. Then
--
--   1. $D(T)\le\varepsilon$;
--   2. $D(U)\ge h-\varepsilon$ for every promised type $U$ with the opposite label;
--   3. if $\varepsilon<h/2$, every promised type minimizing $D$ over the promised types has label $b_T$;
--   4. more generally, if $\zeta\ge0$ and $|\tilde D(U)-D(U)|\le\zeta$ for every promised type $U$, then every promised type minimizing $\tilde D$ has label $b_T$ whenever $\varepsilon+\zeta<h/2$.
--
--   The same decoder is used by the classical protocol and by the quantum upper bound.
--
--   Differences from the source:
--   - reading: minimizing D returns the correct label → every promised type minimizing the score over all promised types has the label of T; reason: the decoder outputs the label of a minimizer; the statement must hold for whichever minimizer is chosen
--   - encoding: known margins → every promised input has histograms ρ, σ; reason: the promise of f lies in one pair of margins
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 3.6, p.12

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_HasLabel
import Definitions.Def_PermInvCC_cutEvents
import Definitions.Def_PermInvCC_hg
import Definitions.Def_PermInvCC_DensDist
import Definitions.Def_PermInvCC_Dscore

namespace PermInvCC

/-- **Lemma 3.6 (Decoding from Hellinger Estimates)** (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, p.12). Fix a permutation-invariant function `f` with known margins and
both output labels, and let `h := h_f`. Let `T` be the true promised type. Suppose probability
distributions `Ĵ^E`, one for each `E ∈ 𝓔`, satisfy `max_E H(J^E_T, Ĵ^E) ≤ ε`. For every promised
type `U` set `D(U) := max_E H(J^E_U, Ĵ^E)`. Then `D(T) ≤ ε`, whereas `D(U) ≥ h − ε` for every
oppositely labelled `U`. In particular, minimizing `D` returns the correct label if `ε < h/2`.
More generally, if `ζ ≥ 0` and `|D̃(U) − D(U)| ≤ ζ` for every promised type `U`, then minimizing
`D̃` returns the correct label whenever `ε + ζ < h/2`.

**Formalization Note.** "Known margins" is the hypothesis that every promised input has
histograms `ρ, σ`. "Minimizing returns the correct label" is read as: every promised type that
minimizes the score over all promised types has the label of `T`. -/
theorem lemma_3_6 (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) (f : PartialFn n q)
    (hf : IsPermInvariant f) (ρ σ : Fin q → ℕ)
    (hmarg : ∀ x y, f x y ≠ none → hist x = ρ ∧ hist y = σ)
    (hboth : (∃ x y, f x y = some true) ∧ (∃ x y, f x y = some false))
    (T : Fin q → Fin q → ℕ) (bT : Bool) (hT : HasLabel f T bT)
    (Jhat : (E : Finset (Fin q × Fin q)) → DensDist E) (hJ : ∀ E ∈ cutEvents q, (Jhat E).IsProb)
    (ε : ℝ) (hacc : Dscore Jhat T ≤ ε) :
    Dscore Jhat T ≤ ε ∧
    (∀ U, HasLabel f U (!bT) → hg f - ε ≤ Dscore Jhat U) ∧
    (ε < hg f / 2 → ∀ U b, HasLabel f U b →
      (∀ U' b', HasLabel f U' b' → Dscore Jhat U ≤ Dscore Jhat U') → b = bT) ∧
    (∀ ζ : ℝ, 0 ≤ ζ → ∀ Dt : (Fin q → Fin q → ℕ) → ℝ,
      (∀ U b, HasLabel f U b → |Dt U - Dscore Jhat U| ≤ ζ) → ε + ζ < hg f / 2 →
      ∀ U b, HasLabel f U b → (∀ U' b', HasLabel f U' b' → Dt U ≤ Dt U') → b = bT) := by sorry

end PermInvCC
