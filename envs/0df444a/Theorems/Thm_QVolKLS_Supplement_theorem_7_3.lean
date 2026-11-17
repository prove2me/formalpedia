-- Prove2me | Theorems.Thm_QVolKLS_Supplement_theorem_7_3
-- name    : QVolKLS.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:36:27.082976+00:00
-- url     : https://prove2.me/theorems/d6365c97-7ecb-4074-921c-9cfde0501e40
-- title:
--   Theorem 7.3 — linear quantum membership-query lower bound
-- statement:
--   There is a universal constant $C>0$ such that, in every dimension $d\ge2$, every unrestricted finite quantum membership-query algorithm which estimates the volume of every promised origin-centered ellipsoid to relative error $1/4$ with probability at least $2/3$ makes at least $\lfloor d/2\rfloor$ membership queries. The promise is
--   $$
--   B(0,1/2)\subseteq K\subseteq B(0,Cd^2).
--   $$
--
--   Thus constant-relative-error volume estimation has worst-case quantum query complexity $\Omega(d)$ even on well-bounded ellipsoids, with arbitrary finite query precision and unrestricted computation between queries.
--
--   **Formalization Note** The algorithm is fixed before $K$ and may use arbitrary workspace, unitaries, deferred intermediate measurements, adaptivity, finitely many coordinate formats, and arbitrary real output decoding. Natural-number division $d/2$ is exactly $\lfloor d/2\rfloor$.
--
--   Differences from the source:
--   - generalization: the printed conclusion is a worst-case $\Omega(d)$ lower bound → Lean states the explicit bound $q\ge\lfloor d/2\rfloor$ established in the proof on p.58; reason: this fixes the hidden lower-bound constant while directly implying the printed claim
--   - encoding: the source allows unrestricted computation and arbitrary finite query precision without a formal circuit syntax → Lean uses arbitrary input-independent unitaries, arbitrary workspace and output decoding, finitely many dyadic formats, and deferred measurement; reason: standard exact coherent-query encoding with the same algorithm class
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Theorem 7.3, p.57, proof pp.57-58

import Definitions.Def_QVolKLS_Supplement_UnrestrictedMemAlgorithm

set_option autoImplicit false

namespace QVolKLS.Supplement

open MeasureTheory

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Theorem 7.3
(Linear quantum query lower bound)**, p.57 (proof through p.58).

There is one universal outer-radius constant `C > 0`. In every dimension `d ≥ 2`, any finite
quantum membership-query algorithm which, for every promised origin-centered ellipsoid, estimates
its volume to relative error `1/4` with probability at least `2/3`, uses at least `⌊d/2⌋` queries.
This is the explicit lower bound established by the proof and implies the printed `Ω(d)` claim.

**Formalization Note.** Algorithms may use any finite set of finite-precision coordinate formats,
arbitrary input-independent unitaries, arbitrary workspace, deferred intermediate measurements and
adaptive control, and arbitrary real output decoding. The body enters only through exact coherent
membership oracles, boundary included. The circuit is fixed before the promised body, so `queries`
is its worst-case query count over those bodies. The explicit `d / 2` is natural-number division,
equal to `⌊d/2⌋`, exactly as proved on p.58.
-/
theorem theorem_7_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ A : UnrestrictedMemAlgorithm d,
        (∀ K : Set (Euc d), OriginEllipsoidPromise C K →
          2 / 3 ≤ A.outProb K (volumeRelativeError K (1 / 4))) →
        d / 2 ≤ A.queries := by sorry

end QVolKLS.Supplement
