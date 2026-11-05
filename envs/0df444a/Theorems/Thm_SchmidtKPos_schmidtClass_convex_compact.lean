-- Prove2me | Theorems.Thm_SchmidtKPos_schmidtClass_convex_compact
-- name    : SchmidtKPos.schmidtClass_convex_compact
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:20.164915+00:00
-- url     : https://prove2.me/theorems/f8b3eaa3-86da-482b-b4d0-a3d3be98e4fa
-- title:
--   p.1 — $S_k$ is a convex compact subset of the density matrices, and $S_k\subseteq S_{k+1}$
-- statement:
--   For all $n$ and $k$, the set $S_k$ of density matrices on $\mathcal H_n\otimes\mathcal H_n$ with Schmidt number at most $k$ satisfies:
--
--   1. $S_k$ is convex;
--   2. $S_k$ is compact;
--   3. $S_k$ is contained in the set $S$ of all density matrices;
--   4. $S_k\subseteq S_{k+1}$.
--
--   Convexity and compactness are what allow a hyperplane to separate a state $\rho\notin S_k$ from $S_k$ in the proof of Theorem 1.
--
--   **Formalization Note** Convexity is over the real numbers. Compactness is in the entrywise topology on matrices.
--
--   Differences from the source:
--   - reading: S_{k−1} ⊂ S_k → S_k ⊆ S_{k+1} for every k; reason: strict inclusion fails for k > n, where both sets are all of S
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, p. 1, "The set Sk is a convex compact subset of the entire set of density matrices denoted by S, and Sk−1 ⊂ Sk"

import Mathlib
import Definitions.Def_SchmidtKPos_schmidtClass
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, p.1: "The set `S_k` is a convex compact subset of the entire set
of density matrices denoted by `S`, and `S_{k−1} ⊂ S_k`."

**Formalization Note.** The inclusion is `⊆`, written `S_k ⊆ S_{k+1}` for every `k`: strict
inclusion fails for `k > n`. Convexity is over `ℝ` (mixtures); compactness is in the entrywise
topology of `Matrix`, the only Hausdorff vector topology in finite dimension. -/
theorem schmidtClass_convex_compact (n k : ℕ) :
    Convex ℝ (schmidtClass n k) ∧ IsCompact (schmidtClass n k) ∧
      schmidtClass n k ⊆ {ρ | QAlgorithms.IsDensityMatrix ρ} ∧
      schmidtClass n k ⊆ schmidtClass n (k + 1) := by sorry

end SchmidtKPos
