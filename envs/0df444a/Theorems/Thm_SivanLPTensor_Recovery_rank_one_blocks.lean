-- Prove2me | Theorems.Thm_SivanLPTensor_Recovery_rank_one_blocks
-- name    : SivanLPTensor.Recovery.rank_one_blocks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:33:05.679693+00:00
-- url     : https://prove2.me/theorems/77406065-55e9-4add-b5f6-ec2d60dc6690
-- title:
--   Corollary 3.3 — Rank-one block recovery
-- statement:
--   Let $m\ge3$, let all mode sizes be positive, and let $T_i=a_i^{(1)}\otimes\cdots\otimes a_i^{(m)}$ have nonzero factors. For every covector frame $P$, its contraction is skew symmetric, has zero diagonal blocks, and for $j<k$,
--   $$\Omega_P(T_i)[j,k]=(-1)^{j+k+1}\det(PF_i[\widehat{j,k}])\,a_i^{(j)}(a_i^{(k)})^\top.$$
--   If the displayed determinant is nonzero, the column and row spans of that block are respectively the lines through $a_i^{(j)}$ and $a_i^{(k)}$. Thus both vectors are recoverable up to nonzero scaling. Skew symmetry determines every lower block.
--   This identifies the factor directions once a component contraction has been isolated; there is no LP assumption for this componentwise identity.
--
--   Differences from the source:
--   - encoding: finite real modes and one-based indices → dependent Fin coordinates with zero-based indices; reason: the same finite arrays; parity in the signed minor formula is unchanged
--   - encoding: vectors recoverable up to scaling from a nonzero rank-one block → its row and column spans equal the two nonzero factor lines; reason: these two lines are exactly the vectors modulo nonzero scalar multiplication
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Corollary 3.3, printed p. 6 / PDF p. 8

import Definitions.Def_SivanLPTensor_Recovery_geometryModel

namespace SivanLPTensor.Recovery
open scoped BigOperators

theorem rank_one_blocks {d : ℕ} {n : Fin (d + 2) → ℕ}
    (hd : 1 ≤ d) (hn : ∀ j, 0 < n j)
    (a : (j : Fin (d + 2)) → Fin (n j) → ℝ) (ha : ∀ j, a j ≠ 0)
    (P : Matrix (Fin d) (BlockIndex n) ℝ) :
    (omega (pureTensor a) P).transpose = -omega (pureTensor a) P ∧
    (∀ j x y, omega (pureTensor a) P ⟨j,x⟩ ⟨j,y⟩ = 0) ∧
    ∀ j k : Fin (d + 2), j < k →
      let E : Matrix (BlockIndex n) (Fin (d + 2)) ℝ := fun x j => embed j (a j) x
      let c := (-1 : ℝ) ^ (j.val + k.val + 1) * Matrix.det (deletedMinor P E j k)
      (∀ x y, omega (pureTensor a) P ⟨j,x⟩ ⟨k,y⟩ = c * a j x * a k y) ∧
      (Matrix.det (deletedMinor P E j k) ≠ 0 →
        (Submodule.span ℝ (Set.range (fun y => fun x => omega (pureTensor a) P ⟨j,x⟩ ⟨k,y⟩)) =
          Submodule.span ℝ {a j}) ∧
        (Submodule.span ℝ (Set.range (fun x => fun y => omega (pureTensor a) P ⟨j,x⟩ ⟨k,y⟩)) =
          Submodule.span ℝ {a k})) := by sorry

end SivanLPTensor.Recovery
