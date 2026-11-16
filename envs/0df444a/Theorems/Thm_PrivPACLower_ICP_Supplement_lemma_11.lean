-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_lemma_11
-- name    : PrivPACLower.ICP.Supplement.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:46.499906+00:00
-- url     : https://prove2.me/theorems/c389a4e7-86c6-4317-9c5d-e01b9b075920
-- title:
--   Lemma 11 (used in the proof of Theorem 5) — threshold packings of boxes, interval unions, halfspaces and polygons
-- statement:
--   For integers $L,k\ge1$ write $(\mathrm{Thr}_L)^k$ for the tuple of $k$ copies of $\mathrm{Thr}_L$.
--
--   1. For $N\ge3$ and $d\ge1$: $(\mathrm{Thr}_{N-1})^d\sqsubseteq B_{N,d}$.
--   2. For $k\ge1$, $N\ge2k$ and $L=\lfloor N/k\rfloor$: $(\mathrm{Thr}_L)^k\sqsubseteq I_{N,k}$.
--   3. For $N\ge3$ and $d\ge1$: $(\mathrm{Thr}_{N-1})^d\sqsubseteq H_{N,d}$.
--   4. For $N,k\ge1$ with $\lfloor\sqrt N\rfloor\ge2k$ and $L=\lfloor\lfloor\sqrt N\rfloor/k\rfloor$: $(\mathrm{Thr}_L)^k\sqsubseteq C_{N,k}$.
--
--   In all four cases the threshold length is at least $2$ ($N-1\ge2$, resp. $L\ge2$). These packings feed Theorem 1 and give the lower bounds of Theorems 5 and 6.
--
--   Differences from the source:
--   - encoding: k >= 1 in item 2 (from "For integers L, k >= 1" on p. 22, needed for N/k) → hypothesis 1 <= k in item 2; reason: the section's standing convention; excludes the undefined division by zero
--   - encoding: the grid [N] = {1, ..., N} (and [N]^d, [N]^2) → Fin N with x standing for x + 1 (real coordinates (x : R) + 1 in halfspaces and halfplanes); reason: a bijective relabelling of the finite domain; no instance changes
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 22, Lemma 11 (proof pp. 22–23). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Supplement_Classes
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem lemma_11 :
    (∀ N d : ℕ, 3 ≤ N → 1 ≤ d →
      Packable (Y := fun _ : Fin d => Fin (N - 1)) (Boxes N d) (fun _ => Thr (N - 1)) ∧
        2 ≤ N - 1) ∧
    (∀ N k : ℕ, 1 ≤ k → 2 * k ≤ N →
      Packable (Y := fun _ : Fin k => Fin (N / k)) (Intervals N k) (fun _ => Thr (N / k)) ∧
        2 ≤ N / k) ∧
    (∀ N d : ℕ, 3 ≤ N → 1 ≤ d →
      Packable (Y := fun _ : Fin d => Fin (N - 1)) (Halfspaces N d) (fun _ => Thr (N - 1)) ∧
        2 ≤ N - 1) ∧
    (∀ N k : ℕ, 1 ≤ N → 1 ≤ k → 2 * k ≤ Nat.sqrt N →
      Packable (Y := fun _ : Fin k => Fin (Nat.sqrt N / k)) (Polygons N k)
          (fun _ => Thr (Nat.sqrt N / k)) ∧
        2 ≤ Nat.sqrt N / k) := by sorry

end PrivPACLower.ICP.Supplement
