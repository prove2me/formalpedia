-- Prove2me | Theorems.Thm_SteinerAPX_port_network_lengths
-- name    : SteinerAPX.port_network_lengths
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:01.870938+00:00
-- url     : https://prove2.me/theorems/68f97a57-04d4-47d7-96e9-4090e33b9590
-- title:
--   §4.1 — shortest networks on the ports of a square have lengths $\sqrt2$, $1+\sqrt3$, $\sqrt2+\sqrt6$ (corrected: opposite ports $2$)
-- statement:
--   Let $b_1,b_2\in\mathbb R^D$ be orthonormal and $z\in\mathbb R^D$. Consider the four ports $z\pm b_1$, $z\pm b_2$ of a square gadget (a square of side $\sqrt2$) and the two ports $z\pm\frac23 b_1$ of a fallback gadget. Then:
--
--   1. two adjacent ports $z+s_1b_1$, $z+s_2b_2$ ($s_1,s_2\in\{\pm1\}$) have $\mathrm{OPT}=\sqrt2$;
--   2. two opposite ports $z\pm b_1$, or $z\pm b_2$, have $\mathrm{OPT}=2$;
--   3. any three of the four ports have $\mathrm{OPT}=1+\sqrt3$;
--   4. all four ports have
--   $$
--   \mathrm{OPT}=\sqrt2+\sqrt6=4-\Delta;
--   $$
--   5. the two fallback ports have $\mathrm{OPT}=\frac43$.
--
--   These lengths are the costs the cable reduction compares: only the four-port network costs less than $\frac43$ per joined pair.
--
--   Differences from the source:
--   - correction: the shortest network joining two ports of a square has length √2 → √2 for two adjacent ports and 2 for two opposite ports; reason: counterexample: the opposite ports z + b₁, z − b₁ are at distance 2 and OPT of two points is their distance (proved in the mission's sanity file), so the printed √2 is false for them; the proof of Lemma 13 only uses "at least √2"
--   - generalization: the ports zs ± b₁, zs ± b₂ (and zs ± (2/3)b₁) with b₁, b₂ orthogonal unit coordinate vectors of ℝᴰ → any centre z and any orthonormal pair b₁, b₂ in any EuclideanSpace ℝ ι; reason: a linear isometry maps any orthonormal pair onto two coordinate vectors and preserves OPT, so the statement specializes to the source's squares
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.13 (PDF p.15), items (a), (b) and the sentence on shortest networks (Figure 3)

import Mathlib
import Definitions.Def_SteinerAPX_Network

namespace SteinerAPX

/-- **Shortest networks on the ports of a square and of a fallback (§4.1), corrected for opposite
ports.** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission
(manuscript sha256 6f78a9ea…), §4.1, p.13 (PDF p.15): "(a) For the square of a triple {u, v, w},
the ports … are the four points zs ± b1 and zs ± b2. They form a square of side length √2. (b) For
the fallback of an element u, the ports ps,0, ps,u are the points zs ± (2/3)b1. They are at
distance 4/3. … The shortest networks joining two, three, or four ports of a square have lengths
√2, 1 + √3, and √2 + √6 = 4 − ∆, respectively (Figure 3)."

For orthonormal `b₁, b₂` and any centre `z` in `ℝᴰ`: two adjacent corners `z ± b₁`, `z ± b₂` have
`OPT = √2`; two opposite corners have `OPT = 2`; any three corners have `OPT = 1 + √3`; all four
have `OPT = √2 + √6`; and the two fallback ports `z ± (2/3)b₁` have `OPT = 4/3`.

**Formalization Note** The printed "two … ports … √2" holds only for adjacent ports: the opposite
corners `z ± b₁` are at distance 2, and the shortest network on two points is their segment. The
statement is corrected minimally (adjacent `√2`, opposite `2`); the proof of Lemma 13 uses only
"at least √2". `OPT` is `opt`, the infimum over spanning networks; each value is claimed exactly. -/
theorem port_network_lengths {ι : Type} [Fintype ι] (z b₁ b₂ : EuclideanSpace ℝ ι)
    (hb : Orthonormal ℝ ![b₁, b₂]) :
    (∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
      opt ({z + s₁ • b₁, z + s₂ • b₂} : Set (EuclideanSpace ℝ ι)) = Real.sqrt 2) ∧
    opt ({z + b₁, z - b₁} : Set (EuclideanSpace ℝ ι)) = 2 ∧
    opt ({z + b₂, z - b₂} : Set (EuclideanSpace ℝ ι)) = 2 ∧
    (∀ p ∈ ({z + b₁, z - b₁, z + b₂, z - b₂} : Set (EuclideanSpace ℝ ι)),
      opt (({z + b₁, z - b₁, z + b₂, z - b₂} : Set (EuclideanSpace ℝ ι)) \ {p}) =
        1 + Real.sqrt 3) ∧
    opt ({z + b₁, z - b₁, z + b₂, z - b₂} : Set (EuclideanSpace ℝ ι)) =
      Real.sqrt 2 + Real.sqrt 6 ∧
    opt ({z + (2 / 3 : ℝ) • b₁, z - (2 / 3 : ℝ) • b₁} : Set (EuclideanSpace ℝ ι)) = 4 / 3 := by sorry

end SteinerAPX
