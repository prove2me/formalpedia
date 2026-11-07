-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_14
-- name    : PathCount2k.lemma_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:20.36433+00:00
-- url     : https://prove2.me/theorems/afc5cb4f-311c-4a76-a31e-cb0d097f40fe
-- title:
--   Lemma 2.14 — the finite estimator $Y_0$ has the moments of $Y$
-- statement:
--   For every integer $D\ge1$, the finite estimator $Y_0=Z_0^2/(k!D^{k-1})$ (samples independent copies of $\xi$) and the Gaussian estimator $Y$ (same $D$) satisfy
--   $$
--   \mathbb E[Y_0]=\mathbb E[Y],\qquad \mathbb E[Y_0^2]=\mathbb E[Y^2].
--   $$
--   In particular $\mathbb E[Y_0]=N$ and $\mathbb E[Y_0^2]\le3(1+2/D)^{k-1}K_kN^2$. If $N=0$, then $Y_0=0$ for every choice of samples.
--
--   The algorithm can therefore run on integer samples and keep the guarantee of the Gaussian analysis.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
--   - encoding: integer samples, independent copies of ξ → real-valued samples under finiteLaw (Measure.pi of xiLaw, supported on {−2, …, 2}); reason: same distributions of the samples
--   - generalization: if N = 0, Y₀ = 0 for every choice of (integer) samples → for every real sample; reason: contains every integer sample
--   - encoding: the expectation E[Y₀²] → Integrable … ∧ the Bochner integral bound; reason: Lean's integral is 0 on a non-integrable function; the paper's expectation exists, so stating integrability excludes only the junk case
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.14, p.13

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_Finite

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.14** (Preservation of estimator moments), p.13: "For every integer
`D ≥ 1`, the finite estimator `Y₀` has the same first two moments as the Gaussian estimator `Y`.
In particular, `E[Y₀] = N` and `E[Y₀²] ≤ 3(1 + 2/D)^{k−1} K_k N²`. If `N = 0`, then `Y₀ = 0` for
every choice of samples."

**Formalization Note.** `Y₀` is integrated against `finiteLaw n k D` (independent copies of `ξ`),
`Y` against `jointLaw n k D` (Gaussian, the same `D`). The integrability of `Y₀²` is stated too.
"Every choice of samples" is every real sample, which contains every integer one. Stated for
every `k ≥ 1` (the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_14 (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D) :
    (∫ ω, Y0 n E k D ω ∂(finiteLaw n k D) = ∫ ω, Y n E k D ω ∂(jointLaw n k D)) ∧
      (∫ ω, Y0 n E k D ω ^ 2 ∂(finiteLaw n k D) = ∫ ω, Y n E k D ω ^ 2 ∂(jointLaw n k D)) ∧
      ∫ ω, Y0 n E k D ω ∂(finiteLaw n k D) = (N n E k : ℝ) ∧
      Integrable (fun ω => Y0 n E k D ω ^ 2) (finiteLaw n k D) ∧
      ∫ ω, Y0 n E k D ω ^ 2 ∂(finiteLaw n k D) ≤
        3 * (1 + 2 / (D : ℝ)) ^ (k - 1) * Kk k * (N n E k : ℝ) ^ 2 ∧
      (N n E k = 0 → ∀ ω, Y0 n E k D ω = 0) := by sorry

end PathCount2k
