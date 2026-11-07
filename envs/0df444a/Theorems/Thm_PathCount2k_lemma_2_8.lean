-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_8
-- name    : PathCount2k.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:57.3342+00:00
-- url     : https://prove2.me/theorems/67780370-f01f-4644-a8c7-c1d482c7a5d9
-- title:
--   Lemma 2.8 — the iterated row bound
-- statement:
--   Let $D\ge1$, $\alpha_D=1+2/D$, $0\le t\le k$, $I$ a finite index set and $a_{h,w}\in\mathbb R$ fixed coefficients for $h\in I$ and $w\in V^t$. With independent auxiliary Gaussian matrices and $R_h=\sum_{w\in V^t}a_{h,w}\,b_0^\top M_{1,w_1}\cdots M_{t,w_t}$,
--   $$
--   \mathbb E_M\Big[\Big(\sum_{h\in I}\|R_h\|^2\Big)^2\Big]\le\alpha_D^{\,t}\Big(\sum_{h\in I}\sum_{w\in V^t}a_{h,w}^2\Big)^2.
--   $$
--
--   This is the tensor-train fourth-moment estimate that controls the dependence created by paths sharing matrices.
--
--   Differences from the source:
--
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
--   - encoding: the expectation E_M[(Σ_h ‖R_h‖²)²] → Integrable … ∧ the Bochner integral bound; reason: Lean's integral is 0 on a non-integrable function; the paper's expectation exists, so stating integrability excludes only the junk case
--   - encoding: the matrices M_{1,·}, …, M_{t,·} of positions 1, …, t → the full matrix law matLaw n k D with t ≤ k (positions after t unused); reason: integrating out unused independent coordinates changes nothing
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.8 with Definition 2.11, p.9

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.8** (Iterated row bound), p.9: "For the rows in Definition 2.11,
`E_M[(∑_{h∈I} ‖R_h‖²)²] ≤ α_D^t (∑_{h∈I} ∑_{w∈V^t} a²_{h,w})²`", where `α_D = 1 + 2/D` (p.8)
and `R_h = ∑_{w ∈ V^t} a_{h,w} b₀ᵀ M_{1,w₁} ⋯ M_{t,w_t}` for `0 ≤ t ≤ k`, a finite index set `I`
and fixed real coefficients `a_{h,w}` (Definition 2.11).

**Formalization Note.** `E_M` is the integral against `matLaw n k D` (the positions `t + 1, …, k`
are unused); the integrability of the left side is stated too. -/
theorem lemma_2_8 (n k D : ℕ) (hD : 1 ≤ D) (I : Type) [Fintype I] (t : ℕ) (ht : t ≤ k)
    (a : I → (Fin t → Fin n) → ℝ) :
    Integrable (fun M => (∑ h : I, sqNorm (rowFamily t ht a M h)) ^ 2) (matLaw n k D) ∧
      ∫ M, (∑ h : I, sqNorm (rowFamily t ht a M h)) ^ 2 ∂(matLaw n k D) ≤
        alpha D ^ t * (∑ h : I, ∑ w : Fin t → Fin n, a h w ^ 2) ^ 2 := by sorry

end PathCount2k
