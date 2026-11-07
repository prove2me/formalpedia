-- Prove2me | Theorems.Thm_SteinerAPX_lemma_13
-- name    : SteinerAPX.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:21.028851+00:00
-- url     : https://prove2.me/theorems/e922b231-aea0-4bfb-9bf6-95c81c7f55b0
-- title:
--   Lemma 13 — good connectors cost $\ge4-\Delta-4\rho$ (square) or $\ge\frac43-2\rho$ (fallback), bad ones $\ge(\frac43-2\rho)(r-1)$
-- statement:
--   Let a well-formed, separated cable layout of a 3DM-3 instance in $\mathbb R^D$ be given, $0<\rho\le1/100$ and $\Delta=4-\sqrt2-\sqrt6$. Let $S$ be a connector with $r$ attachments. Then:
--
--   1. if $S$ is good at a square, $\operatorname{len}(S)\ge4-\Delta-4\rho$;
--   2. if $S$ is good at a fallback, $\operatorname{len}(S)\ge\frac43-2\rho$;
--   3. if $S$ is bad,
--   $$
--   \operatorname{len}(S)\ge\Bigl(\tfrac43-2\rho\Bigr)(r-1).
--   $$
--
--   A good connector is at least as long as the shortest network on the ports of its gadget, and a bad one at least as long as $r-1$ fallback segments, up to errors of order $\rho$.
--
--   Differences from the source:
--   - generalization: S a connector of the tree T̂ (a subtree with leaves on the recovered trees Tᵢ, other points outside them, at least two attachments) → S any network with connected carrier through r points, each within ρ of a distinct cable; reason: the proof uses only these properties; the paper's connectors have them, so the statement specializes to the source's
--   - generalization: b₁, b₂ two orthogonal unit coordinate vectors of ℝᴰ → b₁, b₂ any orthonormal pair (CableLayout.WellFormed) in any EuclideanSpace ℝ ι; reason: a linear isometry of ℝᴰ maps any orthonormal pair onto two coordinate vectors and preserves every quantity in the statement, so the statement specializes to the source's coordinate vectors
--   - encoding: a 3DM-3 instance H with three parts of size r → an Inst3DM, whose parts have size r ≥ 1; reason: excludes only the empty instance (no elements, no triples, no gadgets), which the paper never considers (it assumes 4r ≤ m, §2)
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 13, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_SteinerAPX_Separated
import Definitions.Def_SteinerAPX_Connector

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Lemma 13 (connector lengths).** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*,
STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 13, p.17 (PDF p.19), with `∆ = 4 − √2 −
√6`: "Let S be a connector with r attachments. (i) If S is good at a square, then
len(S) ≥ 4 − ∆ − 4ρ. (ii) If S is good at a fallback, then len(S) ≥ 4/3 − 2ρ. (iii) If S is bad,
then len(S) ≥ (4/3 − 2ρ)(r − 1)."

For a well-formed, separated layout of a 3DM-3 instance in `ℝᴰ`, `0 < ρ ≤ 1/100` and a connector
`S` with `r` attachments (a network with connected carrier through `r` points, each within `ρ` of
a different cable): (i) if `S` is good at a square, `len S ≥ 4 − ∆ − 4ρ`; (ii) if good at a
fallback, `len S ≥ 4/3 − 2ρ`; (iii) if bad, `len S ≥ (4/3 − 2ρ)(r − 1)`.

**Formalization Note** `Connector` keeps only the data the bound depends on (connected network,
attachments on it, each within `ρ` of a distinct cable); the paper's connectors, pieces of a tree
with leaves on the recovered trees `Tᵢ`, satisfy it. `r − 1` is computed in `ℝ`; in the paper
`r ≥ 2`. -/
theorem lemma_13 {ι : Type} [Fintype ι] (H : Inst3DM)
    (L : CableLayout H (EuclideanSpace ℝ ι)) (hH : H.IsThreeDM3) (hL : L.WellFormed)
    (hsep : Separated L) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 100) (C : Connector L ρ) :
    (∀ t : H.triples, C.GoodAt (.inl t) → 4 - Delta - 4 * ρ ≤ len C.S) ∧
    (∀ u : H.Element, C.GoodAt (.inr u) → 4 / 3 - 2 * ρ ≤ len C.S) ∧
    (C.Bad → (4 / 3 - 2 * ρ) * ((C.r : ℝ) - 1) ≤ len C.S) := by sorry

end SteinerAPX
