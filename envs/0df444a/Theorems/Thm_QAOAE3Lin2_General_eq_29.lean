-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_29
-- name    : QAOAE3Lin2.General.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:45.992293+00:00
-- url     : https://prove2.me/theorems/389bc246-2209-4c20-b569-cdc3a0b011ce
-- title:
--   Section II, (29), p. 7 — hypercontractivity: E_z|c|^{k+2} ≤ (k+1)^{k+2}(E_z c²)^{(k+2)/2} for degree-2 c
-- statement:
--   Let $z=(z_1,\dots,z_n)$ be uniform in $\{\pm1\}^n$ and let
--   $$c(z)=a_0+\sum_v a_vz_v+\sum_{u<v}a_{uv}z_uz_v$$
--   be any real polynomial of degree at most $2$. Then for every natural number $k$,
--   $$E_z\big[|c|^{k+2}\big]\le(k+1)^{k+2}\big(E_z[c^2]\big)^{(k+2)/2}.$$
--
--   This is the hypercontractive (Bonami) inequality $\|c\|_q\le(q-1)^{d/2}\|c\|_2$ for degree $d=2$ and $q=k+2$, cited by the paper as Theorem 5 of Dinur–Friedgut–Kindler–O'Donnell. It controls high moments of the clause arguments $d\pm c_1\pm c_2\pm c_3$ by their second moments.
--
--   **Formalization Note.** Every function on $\{\pm1\}^n$ of degree at most $2$ has the multilinear form above, since $z_v^2=1$. The inequality is stated for every $k$, not only the odd $k$ the paper uses. $(E_z[c^2])^{(k+2)/2}$ is written as $\sqrt{E_z[c^2]}^{\,k+2}$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 7, Section II, (29) (citing Dinur, Friedgut, Kindler, O'Donnell, Theorem 5)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_29 (n k : ℕ) (a₀ : ℝ) (a₁ : Fin n → ℝ) (a₂ : Fin n → Fin n → ℝ) :
    let c : QAlgorithms.Qubits n → ℝ := fun x =>
      a₀ + ∑ v, a₁ v * spin x v +
        ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)
    avgZ (fun x => |c x| ^ (k + 2)) ≤
      ((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (avgZ (fun x => c x ^ 2)) ^ (k + 2) := by sorry

end QAOAE3Lin2.General
