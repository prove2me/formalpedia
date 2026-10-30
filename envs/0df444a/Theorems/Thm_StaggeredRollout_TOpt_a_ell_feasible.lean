-- Prove2me | Theorems.Thm_StaggeredRollout_TOpt_a_ell_feasible
-- name    : StaggeredRollout.TOpt.a_ell_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:59:31.228701+00:00
-- url     : https://prove2.me/theorems/8183ff51-5314-4249-98d4-7b3f332d2e2b
-- title:
--   Proof of Theorem 3.1, p. ec22 — a^{(ℓ)} = (A^{(ℓ)})⁻¹b^{(ℓ)} exists and satisfies −1 ≤ ω_t ≤ −1 + (ℓ+1)/(T−ℓ) and ω_t ≤ ω_{t+1}
-- statement:
--   **Feasibility of the second stage of $\omega^*$** (proof of Theorem 3.1, p. ec22).
--
--   Let $\ell\ge1$ and $T>(\ell^3+13\ell^2+7\ell+3)/(8\ell)$. Let $h=\lfloor\ell/2\rfloor$, $K=\ell-h$, and let $M^{(\ell)}$ (called $A^{(\ell)}$ in the proof), $b^{(\ell)}$ be the $K\times K$ matrix and $K$-vector of (EC.1.2)–(EC.1.3). Then:
--
--   1. $M^{(\ell)}$ is invertible, so $a^{(\ell)}=(M^{(\ell)})^{-1}b^{(\ell)}$ is well defined;
--   2. every entry satisfies $\displaystyle -1\le a^{(\ell)}_r\le -1+\frac{\ell+1}{T-\ell}$;
--   3. $a^{(\ell)}_1\le a^{(\ell)}_2\le\dots\le a^{(\ell)}_K$;
--   4. the whole path $\omega^*_{\ell,1},\dots,\omega^*_{\ell,T}$ of (3.4) is nondecreasing;
--   5. $-1\le\omega^*_{\ell,t}\le1$ for every $t$.
--
--   Setting $(\omega_{h+1},\dots,\omega_\ell)=a^{(\ell)}$ solves the stationarity equations (EC.2.10) of the relaxed problem with zero multipliers; these inequalities are what remains to show that this point is feasible, so that $\omega^*$ satisfies the KKT conditions.
--
--   **Formalization Note** $a^{(\ell)}$ is defined with Lean's matrix inverse, so item 1 is what makes it the page's $(A^{(\ell)})^{-1}b^{(\ell)}$. Indices are 0-based (`Fin (ℓ - ℓ/2)`, `Fin T`).
--
--   Differences from the source:
--   - reading: (A^{(ℓ)})⁻¹b^{(ℓ)} written without comment → conclusion (Mmat ℓ T).det ≠ 0; reason: the page presupposes the inverse exists; Lean's ⁻¹ is 0 on singular matrices, so invertibility must be stated
--   - reading: the claim is made inside the proof of Theorem 3.1 for the ℓ with a nonempty second stage → hypotheses 0 < ℓ and (ℓ³ + 13ℓ² + 7ℓ + 3)/(8ℓ) < T; reason: those of Theorem 3.1; for ℓ = 0 the vector a^{(ℓ)} is empty and the claim is void
--   - reading: ω_t ≤ ω_{t+1} for the stage-2 coordinates → Monotone (avec ℓ T); reason: the constraint among the coordinates of a^{(ℓ)}
--   - generalization: constraints for t = ⌊ℓ/2⌋+1, …, ℓ, including the boundary ones ω_{⌊ℓ/2⌋} ≤ ω_{⌊ℓ/2⌋+1} and ω_ℓ ≤ ω_{ℓ+1} → Monotone (omegaStar ℓ T) and −1 ≤ ω*_t ≤ 1 for all t; reason: the page's boundary constraints are instances of global monotonicity; specializes to the page's claim
--   - encoding: A^{(ℓ)} (proof) = M^{(ℓ)} (EC.1.2); 1-based indices → Mmat ℓ T; 0-based Fin indices; reason: the paper uses two names for one matrix; Lean convention
-- source:
--   Xiong, Athey, Bayati, Imbens, Optimal Experimental Design for Staggered Rollouts, arXiv:1911.03764v6, p. ec22 (PDF 58), proof of Theorem 3.1, Case 2, the sentence after (EC.2.10); verified on pp. ec23–ec25

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting

namespace StaggeredRollout.TOpt
open Matrix

theorem a_ell_feasible (ℓ T : ℕ) (hℓ : 0 < ℓ)
    (hT : ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ)) :
    (Mmat ℓ T).det ≠ 0 ∧
    (∀ r, -1 ≤ avec ℓ T r ∧ avec ℓ T r ≤ -1 + ((ℓ : ℝ) + 1) / ((T : ℝ) - ℓ)) ∧
    Monotone (avec ℓ T) ∧
    Monotone (omegaStar ℓ T) ∧
    (∀ t, -1 ≤ omegaStar ℓ T t ∧ omegaStar ℓ T t ≤ 1) := by sorry

end StaggeredRollout.TOpt
