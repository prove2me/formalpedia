-- Prove2me | Theorems.Thm_RegevLWE_SubsetSum_expected_l2_norm
-- name    : RegevLWE.SubsetSum.expected_l2_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:38.775614+00:00
-- url     : https://prove2.me/theorems/d891c8a4-144c-42e1-aa38-2a845f975038
-- title:
--   Proof of Claim 5.3, p. 34:37 — Exp_g[Σ_h P_g(h)²] ≤ 1/2^l + 1/|G|
-- statement:
--   Let $G$ be a finite abelian group and $l \ge 0$. For $g \in G^l$ let $P_g$ be the distribution of the sum of a uniformly random subset of $g_1, \dots, g_l$, $P_g(h) = 2^{-l}|\{b \in \{0,1\}^l \mid \sum_i b_i g_i = h\}|$. Over a uniform choice of $g_1, \dots, g_l \in G$,
--   $$\mathop{\mathrm{Exp}}_{g}\Bigl[\sum_{h \in G} P_g(h)^2\Bigr] \le \frac{1}{2^l} + \frac{1}{|G|}.$$
--
--   Since $\sum_h P_g(h)^2 \ge 1/|G|$ for every distribution on $G$, this says that for $2^l \gg |G|$ the $\ell_2$ norm of $P_g$ is on average close to the minimum $1/|G|$, attained only by the uniform distribution.
--
--   **Formalization Note** $\mathrm{Exp}_g$ is the exact average $|G|^{-l}\sum_{g \in G^l}$ over all $|G|^l$ tuples.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:37, proof of Claim 5.3, first display

import Mathlib
import Definitions.Def_RegevLWE_SubsetSum_Basic

open Finset

namespace RegevLWE.SubsetSum

/-- Proof of Claim 5.3 (Regev, J. ACM 2009, p. 34:37, first display): over a uniform choice of
`g ∈ G^l`, the expected `ℓ₂` norm of `P_g` satisfies `Exp_g[∑_h P_g(h)²] ≤ 1/2^l + 1/|G|`. -/
theorem expected_l2_norm {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (l : ℕ) :
    expectG (fun g : Fin l → G => ∑ h, P g h ^ 2) ≤
      1 / (2 : ℝ) ^ l + 1 / (Fintype.card G : ℝ) := by sorry

end RegevLWE.SubsetSum
