-- Prove2me | Theorems.Thm_PRUPermLayer_Supplement_theorem_1_3
-- name    : PRUPermLayer.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:40:55.000002+00:00
-- url     : https://prove2.me/theorems/87a3dca5-62d2-4176-b778-da2540be698c
-- title:
--   Theorem 1.3 — optimal query dependence: $\frac1{256}\min\{1,t^2(2/3)^n\}\le\mathrm{Adv}^{\mathrm{opt}}_t(PL)\le34\min\{1,t^2(2/3)^n\}$, attained by a product-input collision test
-- statement:
--   Let $N=2^n$ and let $PL$ be the ensemble of Theorem 1.1: a uniformly random permutation unitary $P$ after a layer $L=C_1\otimes\cdots\otimes C_n$ of independent uniformly random single-qubit Clifford gates. Write $\mathrm{Adv}^{\mathrm{opt}}_t(PL)$ for the largest advantage of a $t$-query forward algorithm in distinguishing $PL$ from a Haar-random unitary. For $n\ge4$ and every integer $t\ge2$,
--   $$\frac1{256}\min\Big\{1,\,t^2\Big(\frac23\Big)^n\Big\}\ \le\ \mathrm{Adv}^{\mathrm{opt}}_t(PL)\ \le\ 34\min\Big\{1,\,t^2\Big(\frac23\Big)^n\Big\}.$$
--   Moreover, the lower bound is attained by a non-adaptive algorithm that queries one fixed product state at most $\min\{t,\lfloor(3/2)^{n/2}\rfloor\}$ times and looks for a collision among the measured outputs: for each $n\ge4$ there is a product state $\psi=\varphi_1\otimes\cdots\otimes\varphi_n$ of unit vectors $\varphi_i\in\mathbb C^2$ such that for every $t\ge2$ some $k\le\min\{t,\lfloor(3/2)^{n/2}\rfloor\}$ gives
--   $$\Big|\,\mathbb E_{U\sim PL}\,\mathrm{acc}_{k,\psi}(U)-\mathbb E_{U\sim\mathrm{Haar}}\,\mathrm{acc}_{k,\psi}(U)\Big|\ \ge\ \frac1{256}\min\Big\{1,\,t^2\Big(\frac23\Big)^n\Big\},$$
--   where $\mathrm{acc}_{k,\psi}(U)$ is the acceptance probability of the $k$-query collision test on $\psi$ with oracle $U$.
--
--   The theorem identifies the optimal forward-query advantage up to constant factors for every number of queries, including exponentially many: it grows like $t^2(2/3)^n$ below about $(3/2)^{n/2}$ queries and is constant beyond.
--
--   **Formalization Note** $\mathrm{Adv}^{\mathrm{opt}}_t(PL)$ is the mission's published `advOpt n t (plEnsemble n)`. The truncation $k\le\lfloor(3/2)^{n/2}\rfloor$ is written $k\le(3/2)^{n/2}$ with a real exponent, which is equivalent for natural $k$ and allows odd $n$. The attainment clause also asserts that the two acceptance functions are integrable (they are continuous and bounded on the compact unitary group), so that both expectations are genuine.
--
--   Differences from the source:
--   - generalization: "the lower bound is attained by a non-adaptive algorithm that queries one fixed product state" for each t → one product state chosen for each n and used for every t ≥ 2, with a k ≤ min{t, ⌊(3/2)^{n/2}⌋} for each t; reason: a single state for all t is stronger and specializes to the source's per-t claim; the proof's state |m⟩^{⊗n} does not depend on t
--   - encoding: k ≤ ⌊(3/2)^{n/2}⌋ → (k : ℝ) ≤ (3/2)^{n/2} with a real exponent; reason: equivalent for natural k
--   - encoding: the test's advantage → |∫ acc dPL − ∫ acc dHaar| together with integrability of acc for both measures; reason: acc is continuous and bounded on the compact group, so the integrability conjuncts hold and only rule out the junk value 0 of a Bochner integral
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa33ec861a7e9c10d88cfcefc2794b77ad1674c02661c9298c5ba565bcb), Theorem 1.3, p.3 (PDF p.5); proof §7, pp.24–25 (PDF pp.26–27)

import Mathlib
import Definitions.Def_PRUPermLayer_advOpt
import Definitions.Def_PRUPermLayer_plEnsemble
import Definitions.Def_PRUPermLayer_haar
import Definitions.Def_PRUPermLayer_Supplement_productCollisionAccept
open MeasureTheory

namespace PRUPermLayer.Supplement

/-- **Theorem 1.3** (optimal query dependence; Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Theorem 1.3, p.3 (PDF p.5); proof §7,
pp.24–25 (PDF pp.26–27)). Let `L` be as in Theorem 1.1 (i.i.d. uniformly random single-qubit
Clifford gates) and `N = 2ⁿ`. For `n ≥ 4` and every integer `t ≥ 2`,
`(1/256) min{1, t²(2/3)ⁿ} ≤ Adv^opt_t(PL) ≤ 34 min{1, t²(2/3)ⁿ}`.
The lower bound is attained by a non-adaptive algorithm that queries one fixed product state at
most `min{t, ⌊(3/2)^{n/2}⌋}` times and looks for a collision among the measured outputs.

**Formalization Note** `Adv^opt_t(PL)` is the published `advOpt n t (plEnsemble n)` (supremum over
all `t`-query forward algorithms against `haar n`). The attainment clause: there is one product
input `φ₀ ⊗ ⋯ ⊗ φ_{n−1}` (unit vectors `φ i : Bool → ℂ`), chosen once for the given `n` and used
for every `t`, such that for each `t ≥ 2` some number of queries `k` with `k ≤ t` and
`k ≤ (3/2)^{n/2}` (a real power; for `k ∈ ℕ` this is `k ≤ ⌊(3/2)^{n/2}⌋`) gives the collision test
`productCollisionAccept n k φ` advantage `|E_{PL} acc − E_{Haar} acc|` at least the lower bound.
That test makes `k ≤ t` forward queries. The two `Integrable` conjuncts (true: the acceptance
probability is continuous and bounded on the compact group) make both expectations genuine, not the
junk value `0`. -/
theorem theorem_1_3 (n : ℕ) (hn : 4 ≤ n) :
    (∀ t : ℕ, 2 ≤ t →
      (1 / 256 : ℝ) * min 1 ((t : ℝ) ^ 2 * (2 / 3 : ℝ) ^ n) ≤ advOpt n t (plEnsemble n) ∧
        advOpt n t (plEnsemble n) ≤ 34 * min 1 ((t : ℝ) ^ 2 * (2 / 3 : ℝ) ^ n)) ∧
    ∃ φ : Fin n → Bool → ℂ, (∀ i, ∑ b, ‖φ i b‖ ^ 2 = 1) ∧
      ∀ t : ℕ, 2 ≤ t → ∃ k : ℕ, k ≤ t ∧ (k : ℝ) ≤ (3 / 2 : ℝ) ^ ((n : ℝ) / 2) ∧
        Integrable (fun U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ =>
          productCollisionAccept n k φ (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (plEnsemble n) ∧
        Integrable (fun U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ =>
          productCollisionAccept n k φ (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (haar n) ∧
        (1 / 256 : ℝ) * min 1 ((t : ℝ) ^ 2 * (2 / 3 : ℝ) ^ n) ≤
          |(∫ U, productCollisionAccept n k φ (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
              ∂(plEnsemble n)) -
            ∫ U, productCollisionAccept n k φ (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
              ∂(haar n)| := by sorry

end PRUPermLayer.Supplement
