-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_4_7
-- name    : ReLUSynth.Boolean.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:11:27.415197+00:00
-- url     : https://prove2.me/theorems/b2ca95c9-750a-47be-a73b-f214515e7ad6
-- title:
--   Lemma 4.7 — some query block is clean; the restricted target g is a threshold no affine-plus-one-ReLU function realizes, robustly under small fixings
-- statement:
--   For the calibrated construction:
--   1. For every legal candidate with cap four, some query block has no input edge from its coordinates carrying an occurrence outside the query-baseline family; so each input edge from a coordinate of that block carries an actual value $F2^{i'}+2w$, where $i'$ is the level of the occurrence.
--   2. Fixing every coordinate outside a block to zero, the target restricts to
--   $$g(y)=1\iff\sum_{i=0}^{r-1}\sum_{\gamma=1}^3 2^iy_{i,\gamma}\ge Q .$$
--   3. The origin and all unit vectors lose; the all-ones vector and every one- or two-coordinate deletion win.
--   4. Every query coordinate is essential for $g$.
--   5. Neither $g$, nor any restriction of $g$ obtained by fixing up to two coordinates to zero or any one coordinate to one, can be written as $\ell(y)+a\,\rho(s+v\cdot y)$ with $\ell$ affine and $a,s\in\mathbb R$, $v\in\mathbb R^{3r}$.
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - generalization: an instance in the hardness family produced by Lemma 4.5 (p. 19) → any instance satisfying every restriction listed in Lemma 4.5 (CalibData.Valid: q ≥ 5 prime, 0 < β_j < T, β_j not a power of two, β_j ≡ 3, T ≡ 0 (mod q), n > p); reason: the proofs on pp. 19–27 and in Appendix A use only these restrictions; every instance the reduction produces satisfies them, so the Lean statement specializes to the paper's
--   - reading: choose an odd prime r, powers of two F and M satisfying the displayed inequalities (pp. 19–20) → every choice of r, F, M satisfying those inequalities (strictly, as printed); reason: the page leaves the choice free among the values satisfying the inequalities, and its lemmas are claimed for the construction so chosen
--   - encoding: a candidate / legal assignment (in §4 and Appendix A, legal = at-most-once, p. 10) with computational-node cap four → Net.Permitted InventoryRule.atMostOnce 4 on the occurrence type Occ c of the calibrated inventory; reason: exactly-once networks are among these, as the paper notes (p. 10)
--   - generalization: the target restriction is g for the block found in part 1 → for every query block b, f restricted to block b with all other coordinates zero equals g; reason: f treats all blocks alike, so the restriction is g for each block; it specializes to the found block
--   - encoding: a restriction of g obtained by fixing coordinates, expressed as an affine function plus a multiple of one ReLU of an affine function → no c₀, ℓ, a, s, v with g(y) = c₀ + ℓ·y + aρ(s + v·y) for every y on the face (fixed coordinates at their values); reason: on a face the fixed coordinates are constants, so affine forms in all coordinates are exactly affine forms in the free ones
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 22, Lemma 4.7

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Calibrated

namespace ReLUSynth.Boolean

/-- Lemma 4.7 (p. 22). (1) For every legal candidate with cap four, some query block has no input
edge from its coordinates carrying an occurrence outside the query-baseline family, so each such
edge carries an actual value `F2^{i'} + 2w`, `i'` the level of the occurrence. (2) Fixing every
coordinate outside a block to zero, the target restricts to `g(y) = 1 ⟺ ∑_i ∑_γ 2^i y_{i,γ} ≥ Q`.
(3) The origin and all unit vectors lose; the all-ones vector and every one- or two-coordinate
deletion win. (4) Every query coordinate is essential. (5) Neither `g` nor any restriction of `g`
fixing up to two coordinates to zero or one coordinate to one is an affine function plus a scalar
multiple of one ReLU of an affine function. -/
theorem lemma_4_7 (c : CalibData) (hc : c.Valid) :
    (∀ N : Net (Coord c) (Occ c), N.Permitted InventoryRule.atMostOnce 4 →
      ∃ b : Fin c.J, ∀ (i : Fin c.r) (γ : Fin 3) (v : Fin (N.h + 1)) (o : Occ c),
        N.occ (.inEdge (.query b i γ) v) = some o →
          ∃ (b' : Fin c.J) (i' : Fin c.r) (γ' : Fin 3) (k : Fin 2),
            o = .base (.query b' i' γ') k ∧ c.inv o = (c.F : ℚ) * 2 ^ i'.val + 2 * c.w) ∧
    (∀ (b : Fin c.J) (y : Fin c.r × Fin 3 → Bool),
      c.target (c.blockEmbed b y) = queryTarget c.r y) ∧
    queryTarget c.r (fun _ => false) = false ∧
    (∀ p : Fin c.r × Fin 3, queryTarget c.r (fun p' => decide (p' = p)) = false) ∧
    (∀ S : Finset (Fin c.r × Fin 3), S.card ≤ 2 →
      queryTarget c.r (fun p => decide (p ∉ S)) = true) ∧
    (∀ p : Fin c.r × Fin 3, ∃ y : Fin c.r × Fin 3 → Bool,
      queryTarget c.r (Function.update y p false) ≠ queryTarget c.r (Function.update y p true)) ∧
    (∀ fix : Fin c.r × Fin 3 → Option Bool,
      (((∀ p, fix p ≠ some true) ∧ (Finset.univ.filter (fun p => fix p ≠ none)).card ≤ 2) ∨
        (∃ p₀, fix p₀ = some true ∧ ∀ p, p ≠ p₀ → fix p = none)) →
      ¬ ∃ (c₀ a s : ℝ) (ℓ v : Fin c.r × Fin 3 → ℝ), ∀ y : Fin c.r × Fin 3 → Bool,
        (∀ p bit, fix p = some bit → y p = bit) →
          bitR (queryTarget c.r y) =
            c₀ + ∑ p, ℓ p * bitR (y p) + a * Net.relu (s + ∑ p, v p * bitR (y p))) := by sorry

end ReLUSynth.Boolean
