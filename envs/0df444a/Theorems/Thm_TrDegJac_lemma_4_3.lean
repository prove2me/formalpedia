-- Prove2me | Theorems.Thm_TrDegJac_lemma_4_3
-- name    : TrDegJac.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:56.765149+00:00
-- url     : https://prove2.me/theorems/79ad2f66-200f-4af5-b9b4-99b34812d842
-- title:
--   Lemma 4.3 — $[E(\gamma):E]\le[\mathbb F(\gamma):\mathbb F]$
-- statement:
--   Let $\mathbb F\subseteq E\subseteq K$ be fields and let $\gamma\in K$ be algebraic over $\mathbb F$. Then
--   $$
--   [E(\gamma):E]\ \le\ [\mathbb F(\gamma):\mathbb F].
--   $$
--
--   Enlarging the base field can only lower the degree of an element; this drives the greedy ordering of Lemma 4.11.
--
--   **Formalization Note** The tower is given by algebra maps with `IsScalarTower F E K`; degrees are `Module.rank`.
--
--   Differences from the source:
--   - encoding: fields K ⊇ E, F with E ⊇ F → fields F, E, K with algebra maps F → E → K, F → K and IsScalarTower F E K; reason: maps between fields are injective, so this is the same tower up to isomorphism
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 4.3, p.26

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **Lemma 4.3** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.26:
"If K ⊇ E, F and E ⊇ F and γ ∈ K is algebraic over F then [E(γ) : E] ≤ [F(γ) : F]."

**Formalization Note.** The tower `F ⊆ E ⊆ K` is given by algebra maps (injective, as these are
fields) with `IsScalarTower F E K`. `E(γ)` and `F(γ)` are `IntermediateField.adjoin` inside `K`,
and degrees are `Module.rank` (both are finite since `γ` is algebraic over `F`). -/
theorem lemma_4_3 {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K]
    [Algebra F K] [IsScalarTower F E K] (γ : K) (hγ : IsAlgebraic F γ) :
    Module.rank E (IntermediateField.adjoin E {γ}) ≤
      Module.rank F (IntermediateField.adjoin F {γ}) := by sorry

end TrDegJac
