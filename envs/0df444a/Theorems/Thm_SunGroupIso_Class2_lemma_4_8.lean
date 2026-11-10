-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_4_8
-- name    : SunGroupIso.Class2.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:15.094299+00:00
-- url     : https://prove2.me/theorems/5baf0c66-0060-4ff1-aea1-6fc58f00d99f
-- title:
--   Lemma 4.8 — k elements lie in a direct summand with at most bk cyclic factors
-- statement:
--   Let $G$ be a finite abelian $p$-group of exponent $p^b$ and $g_1,\dots,g_k\in G$. Then there are $m\le bk$ elements $x_1,\dots,x_m\in G$ and $K\le G$ with $G=\langle x_1\rangle\oplus\cdots\oplus\langle x_m\rangle\oplus K$ and every $g_i\in\langle x_1\rangle\oplus\cdots\oplus\langle x_m\rangle$.
--
--   Differences from the source: none.
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.8, p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_Basic

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 4.8** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.8, p. 17, PDF p. 19). Let `G` be a finite abelian `p`-group of exponent
`p^b` and `g_1, …, g_k ∈ G`. Then there are `m ≤ bk` elements `x_1, …, x_m ∈ G` and `K ≤ G` with
`G = ⟨x_1⟩ ⊕ ⋯ ⊕ ⟨x_m⟩ ⊕ K` and every `g_i ∈ ⟨x_1⟩ ⊕ ⋯ ⊕ ⟨x_m⟩`. -/
theorem lemma_4_8 {p : ℕ} (hp : p.Prime) {G : Type*} [CommGroup G] [Finite G] (hG : IsPGroup p G)
    (b : ℕ) (hb : Monoid.exponent G = p ^ b) (k : ℕ) (g : Fin k → G) :
    ∃ m ≤ b * k, ∃ x : Fin m → G, ∃ K : Subgroup G,
      DecompWith ⊤ x K ∧ ∀ i, g i ∈ Subgroup.closure (Set.range x) := by sorry

end SunGroupIso.Class2
