-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_3
-- name    : PathCount2k.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:27.096196+00:00
-- url     : https://prove2.me/theorems/f84b67ec-bea6-4dbf-8019-bebebf55f305
-- title:
--   Lemma 2.3 — $\mathbb E_M[\chi(P)\chi(Q)]=[P=Q]$
-- statement:
--   Fix an integer $D\ge1$ and let the auxiliary matrices $M_{i,v}\in\mathbb R^{D\times D}$ have independent $N(0,1/D)$ entries. For all directed $k$-vertex paths $P,Q\in\mathcal P_k$, with $\chi(P)=\sqrt D\,b_0^\top M_{1,v_1}\cdots M_{k,v_k}b_0$,
--   $$
--   \mathbb E_M\big[\chi(P)\chi(Q)\big]=\begin{cases}1,&P=Q,\\0,&P\neq Q,\end{cases}
--   $$
--   the expectation being over the matrices.
--
--   The random matrix products replace independent random signs on the paths while being computable by dynamic programming.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
--   - encoding: the expectation E_M[χ(P)χ(Q)] → Integrable … ∧ the Bochner integral bound; reason: Lean's integral is 0 on a non-integrable function; the paper's expectation exists, so stating integrability excludes only the junk case
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.3, p.6 (proof p.7)

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.3**, p.6: "For every `P, Q ∈ P_k`, `E_M[χ(P)χ(Q)]` equals `1` if `P = Q`
and `0` otherwise, where the expectation is over the auxiliary matrices."

Here `χ(P) = √D b₀ᵀ M_{1,v₁} ⋯ M_{k,v_k} b₀` (Definition 2.7) and the entries of the matrices
`M_{i,v}` are independent `N(0, 1/D)` (Definition 2.6), `D ≥ 1`.

**Formalization Note.** `E_M` is the integral against `matLaw n k D`; the integrability of
`χ(P)χ(Q)` is stated too. Stated for every `k ≥ 1` (the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_3 (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D)
    (P Q : Fin k → Fin n) (hP : P ∈ paths n E k) (hQ : Q ∈ paths n E k) :
    Integrable (fun M => chi M P * chi M Q) (matLaw n k D) ∧
      ∫ M, chi M P * chi M Q ∂(matLaw n k D) = if P = Q then 1 else 0 := by sorry

end PathCount2k
