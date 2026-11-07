-- Prove2me | Theorems.Thm_PRUPermLayer_lemma_3_1
-- name    : PRUPermLayer.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:30:57.575628+00:00
-- url     : https://prove2.me/theorems/c976bccd-9d99-47ee-8280-fe5f0aa0e453
-- title:
--   Lemma 3.1 — compilation lemma: $\mathrm{Adv} \le \min\{1, \eta_t(D) + 28t^2/N\}$
-- statement:
--   Let $N = 2^n$, let $D$ be any distribution on $U(N)$, and let $t \ge 1$ satisfy $t^2 \le N/4$. Every $t$-query forward algorithm distinguishes $PC$, with $P$ a uniformly random permutation and $C \sim D$ independent of $P$, from a Haar-random unitary with advantage at most
--   $$
--   \min\Big\{1,\ \eta_t(D) + \frac{28\,t^2}{N}\Big\}.
--   $$
--
--   The adaptive security of $PC$ thus depends on $D$ only through its DNP failure $\eta_t(D)$; for a unitary 2-design it recovers [FLM+26, Theorem 7.34].
--
--   Differences from the source:
--   - encoding: $t^2 \le N/4$ → $4t^2 \le 2^n$ in $\mathbb N$; reason: equivalent for integers
--   - encoding: a distribution $D$ on $U(N)$ → a Borel probability measure on $U(N)$; reason: same objects
--   - generalization: an algorithm that measures and outputs one bit, with a workspace and a reference register → any final effect $0 \preceq M \preceq I$ and any number $m$ of extra qubits; reason: effects include projective measurements, and every finite workspace embeds in qubits, so the source's algorithms are among the Lean ones
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 3.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_PRUPermLayer_advantage
import Definitions.Def_PRUPermLayer_pcEnsemble
import Definitions.Def_PRUPermLayer_haar
import Definitions.Def_PRUPermLayer_eta
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Lemma 3.1** (compilation lemma; Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 3.1, p.12 (PDF p.14)). Let `D` be any
distribution on `U(N)`, `N = 2ⁿ`, and let `t ≥ 1` satisfy `t² ≤ N/4`. Every `t`-query forward
algorithm distinguishes `PC`, with `P` a uniformly random permutation and `C ∼ D` independent of
`P`, from a Haar-random unitary with advantage at most `min{1, η_t(D) + 28 t²/N}`.

**Formalization Note** `t² ≤ N/4` is `4 * t ^ 2 ≤ 2 ^ n` in `ℕ` (equivalent). A distribution is a
probability measure on the Borel σ-algebra of `U(N)`. -/
theorem lemma_3_1 (n t : ℕ) (D : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ))
    [IsProbabilityMeasure D] (ht : 1 ≤ t) (htN : 4 * t ^ 2 ≤ 2 ^ n) (alg : FwdAlg n t) :
    advantage alg (pcEnsemble D) (haar n) ≤
      min 1 (eta n t D + 28 * (t : ℝ) ^ 2 / 2 ^ n) := by sorry

end PRUPermLayer
