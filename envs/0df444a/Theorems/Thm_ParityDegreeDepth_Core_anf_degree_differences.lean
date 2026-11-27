-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_anf_degree_differences
-- name    : ParityDegreeDepth.Core.anf_degree_differences
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:34.157567+00:00
-- url     : https://prove2.me/theorems/baf465d8-4b8f-459f-8cb6-5146d3878bd8
-- title:
--   ANF degree versus finite differences
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ with algebraic normal form $p(x)=\sum_{S\subseteq[n]}c_S\prod_{i\in S}x_i$, where $c_S=\sum_{B\subseteq S}p(\mathbf 1_B)$ (Möbius formula (14)). Then:
--
--   1. if $c_S=0$ for all $|S|>d$ (ANF degree at most $d$), then every $(d+1)$-fold finite difference vanishes: $\Delta_{h_1}\cdots\Delta_{h_{d+1}}p\equiv0$;
--   2. if $p$ is affine ($p(x+u+v)+p(x+u)+p(x+v)+p(x)=0$ for all $x,u,v$), then $c_S=0$ for every $|S|\ge2$.
--
--   Thus the ANF degree used in the statement of Theorem 1.3 controls the finite-difference degree used in the proof, and a phase of ANF degree $d\ge2$ is not affine.
--
--   **Formalization Note** $c_S$ is computed exactly as in the statement of Theorem 1.3, via `ParityCubes.anfCoeff` on the Boolean version of $p$.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Appendix A.4 (algebraic normal form, Möbius formula eq. (14), finite differences lower the degree), pp. 18-19; ANF coefficients as in ParityCubes.anfCoeff

import Mathlib
import Definitions.Def_ParityCubes_anfCoeff

theorem ParityDegreeDepth.Core.anf_degree_differences {n d : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) :
    ((∀ S : Finset (Fin n), d < S.card →
        (if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
          then (1 : ZMod 2) else 0) = 0) →
      ∀ (h : Fin (d + 1) → Fin n → ZMod 2) (x : Fin n → ZMod 2),
        (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p x = 0) ∧
    ((∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0) →
      ∀ S : Finset (Fin n), 2 ≤ S.card →
        (if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
          then (1 : ZMod 2) else 0) = 0) := by sorry
