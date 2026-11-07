-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_5
-- name    : PathCount2k.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:09.172874+00:00
-- url     : https://prove2.me/theorems/7d308c66-2ba8-430d-8782-c8df7c64d2ef
-- title:
--   Lemma 2.5 — fourth-moment bound $\mathbb E[Z^4]\le3(1+2/D)^{k-1}K_k(k!)^2N^2$
-- statement:
--   Let $K_k=(k+1)(k+2)/2$. For every integer $D\ge1$, under independent Gaussian vertex vectors and auxiliary matrices,
--   $$
--   \mathbb E[Z^4]\le3\Big(1+\frac2D\Big)^{k-1}K_k\,(k!)^2N^2.
--   $$
--
--   With $D=k$ this gives $\mathbb E[Y^2]\le C_kN^2$, $C_k=3e^2K_k=O(k^2)$, so $O(k^2\varepsilon^{-2})$ trials per group suffice.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
--   - encoding: the expectation E[Z⁴] → Integrable … ∧ the Bochner integral bound; reason: Lean's integral is 0 on a non-integrable function; the paper's expectation exists, so stating integrability excludes only the junk case
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.5, p.8 (proof p.12)

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.5** (Fourth-moment bound), p.8: "Let `K_k = (k + 1)(k + 2)/2`. For every
integer `D ≥ 1`, we have `E[Z⁴] ≤ 3(1 + 2/D)^{k−1} K_k(k!)²N²`."

**Formalization Note.** `E` is the integral against `jointLaw n k D`; the integrability of `Z⁴` is
stated too. Stated for every `k ≥ 1` (the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_5 (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D) :
    Integrable (fun ω => Z n E k D ω ^ 4) (jointLaw n k D) ∧
      ∫ ω, Z n E k D ω ^ 4 ∂(jointLaw n k D) ≤
        3 * (1 + 2 / (D : ℝ)) ^ (k - 1) * Kk k * (Nat.factorial k : ℝ) ^ 2 * (N n E k : ℝ) ^ 2 := by sorry

end PathCount2k
