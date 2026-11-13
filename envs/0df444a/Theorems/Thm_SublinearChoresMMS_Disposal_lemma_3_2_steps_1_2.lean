-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_2_steps_1_2
-- name    : SublinearChoresMMS.Disposal.lemma_3_2_steps_1_2
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T10:01:14.008679+00:00
-- url     : https://prove2.me/theorems/88a5086c-ab7a-479a-a33d-795b11c58333
-- title:
--   Lemma 3.2, Appendix A.2 Steps 1–2 — every linear functional is matched by a coordinated vector with few mixed agents
-- statement:
--   The proof of Lemma 3.2 (Appendix A.2, printed p. 26) says: "We first show that, for every linear functional $f$, some $\zeta \in S$ satisfies $f(\zeta) = f(\eta)$." Steps 1–2 of that proof (printed pp. 26–27) carry it out with Bansal's randomized rounding [Ban24, Theorem 1.2 and Section 3.2.1]. This statement formalizes that claim; Step 3 (hyperplane separation) then turns it into the lottery of `SublinearChoresMMS.Disposal.lemma_3_2`.
--
--   **Statement.** For every $B > 0$ there are $C_4 > 0$ and $n_0 \ge 2$ such that the following holds. Let $n \ge n_0$, $q$ = `blockSize n` $= 2^{\lfloor \log_2 \sqrt{n \ln n} \rfloor}$, $L = \lfloor n/q \rfloor$, and let the costs $c$ be `Normalized` (positive, strictly decreasing in the chore index, $\mu_i = 1$). Assume $q \le m$, $q \mid m$, a reserved set $R$ with $1 \le |R| < n$, and $4 \ln n \le q$. For each ordinary agent $i \notin R$, let $p_i$ be a valid packing (`ValidPacking`) whose `segments` count is at most $B L^3$. Write $x_{i,t}$ = `completed c p i t` for the completed fractional bundles of §3.1, $\eta_t$ = `eta n q t` $= d_t/n$, and $\Gamma$ = `profiles c p` for the number of distinct vectors $(x_{i,t}(e))_{i,t}$ as $e$ ranges over the chores. Then for every real array $\varphi = (\varphi_{i,t})$ on ordinary agents and $t < L$ there is a real array $\zeta$ on the same index set such that:
--   - every row of $\zeta$ lies in the simplex (`Simplex`);
--   - for every reserved $j \in R$, $\sum_{i,t} \zeta_{i,t}\, c_j(x_{i,t}) = (n-|R|)\,\mathrm{PROP}_j$;
--   - at most $2(|R|+1)$ ordinary agents are mixed, that is, have a row that is not a unit vector (`mixedCount`);
--   - for every chore $e$, $\bigl|\sum_{i,t} (\zeta_{i,t} - \eta_t)\, x_{i,t}(e)\bigr| \le \frac{C_4}{2}\sqrt{\ln(2\Gamma)/q}$;
--   - $\sum_{i,t} \varphi_{i,t}\, \zeta_{i,t} = \sum_{i,t} \varphi_{i,t}\, \eta_t$.
--
--   The first four conditions say that $\zeta$ belongs to the paper's set $S$. The fifth is $f(\zeta) = f(\eta)$ for the linear functional $f(\zeta) = \sum_{i,t} \varphi_{i,t}\zeta_{i,t}$; every linear functional on the coefficient space has this form. The paper fixes $C_4$ as a sufficiently large absolute constant. Here $C_4$ and $n_0$ may depend on $B$, the constant in the segment bound of Lemma 3.1, because the paper's bound $\Gamma = O(n L^3)$ does.
--
--   **Route (the paper's).** Run Bansal's rounding from $\eta$ with parameter $1/4$. Keep active the agent-sum equations, the $|R|$ reserved cost equations and $f(\zeta) = f(\eta)$. Stop once at most $4(|R|+1)$ coordinates are fractional. While more remain, the rank condition holds, because a mixed agent has at least two fractional coordinates. The variance bound $\sum_{i,t} x_{i,t}(e)^2 \eta_t (1-\eta_t) \le 1/q$ and Bansal's concentration bound for the stopped process then give a tail at most $1/(2\Gamma)$ for each of the $\Gamma$ distinct profiles. A union bound shows that $\zeta \in S$ with probability at least $1/2$.
--
--   [Ban24] N. Bansal, *On a generalization of iterated and randomized rounding*, Theory of Computing 20(6) (2024) 1–23, https://doi.org/10.4086/toc.2024.v020a006.
-- source:
--   Lin, Wu, Zhou, Best-of-Many-Worlds MMS Allocation for Chores with Sublinear Disposals (STOC 2027 submission 845), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf, pp. 26–27, Appendix A.2, proof of Lemma 3.2, Steps 1–2 (printed pp. 26–27 / PDF pp. 27–28), using Bansal, On a generalization of iterated and randomized rounding, Theory of Computing 20(6) (2024) 1–23, https://doi.org/10.4086/toc.2024.v020a006, Theorem 1.2 and Section 3.2.1

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Prepared

noncomputable section

namespace SublinearChoresMMS.Disposal

theorem lemma_3_2_steps_1_2 (B : ℝ) (hB : 0 < B) :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (c : Cost n m),
        Normalized c → blockSize n ≤ m → blockSize n ∣ m →
        ∀ R : Finset (Fin n), 1 ≤ R.card → R.card < n →
          4 * Real.log n ≤ (blockSize n : ℝ) →
          ∀ p : Packings n m (blockSize n) R,
            (∀ i, ValidPacking c i.val (p i)) →
            (∀ i, (segments (p i) : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3) →
            ∀ φ : Coefficients n (blockSize n) R,
              ∃ ζ : Coefficients n (blockSize n) R,
                Simplex ζ ∧
                (∀ j ∈ R, (∑ i, ∑ t, ζ i t * fractionalCost c j (completed c p i t)) =
                  ((n - R.card : ℕ) : ℝ) * propShare c j) ∧
                mixedCount ζ ≤ 2 * (R.card + 1) ∧
                (∀ e, |∑ i, ∑ t, (ζ i t - eta n (blockSize n) t) * completed c p i t e| ≤
                  C₄ / 2 * Real.sqrt (Real.log (2 * (profiles c p : ℝ)) / blockSize n)) ∧
                (∑ i, ∑ t, φ i t * ζ i t) = ∑ i, ∑ t, φ i t * eta n (blockSize n) t := by
  sorry

end SublinearChoresMMS.Disposal
