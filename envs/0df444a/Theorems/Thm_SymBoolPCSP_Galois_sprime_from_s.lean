-- Prove2me | Theorems.Thm_SymBoolPCSP_Galois_sprime_from_s
-- name    : SymBoolPCSP.Galois.sprime_from_s
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:51.955911+00:00
-- url     : https://prove2.me/theorems/f0d9fa39-9894-495f-902b-e743a58b166a
-- title:
--   Proof of Theorem 6.1 — (S′_m, T′_m) is ppp-definable from (S_m, T_m)
-- statement:
--   Let $D$ be a finite domain, $\Gamma$ a finite family of promise relations on $D$, $m, k \ge 0$, and $x^1, \dots, x^m \in D^k$. Define $y^1, \dots, y^k \in D^m$ by $y^i_j = x^j_i$, and
--   $$S'_m = \{(f(y^1), \dots, f(y^k)) : f \in S_m\}, \qquad T'_m = \{(f(y^1), \dots, f(y^k)) : f \in T_m\},$$
--   with $S_m, T_m$ as in Proposition 6.3. Then $(S'_m, T'_m)$ is ppp-definable from the one-relation family $\{(S_m, T_m)\}$, where functions $D^m \to D$ are listed as vectors of their $|D|^m$ values.
--
--   In the proof of Theorem 6.1 the vectors $x^1, \dots, x^m$ enumerate $P'$; the statement holds for any vectors. Repeated vectors $y^i = y^j$ are allowed, which is where the EQUAL relation is used.
--
--   **Formalization Note** The vectors are a function `x : Fin m → Fin k → D` (`x j` is $x^{j}$, 0-based), and $y^i_j$ is `x j i` (`yvec`). The ordering of the $|D|^m$ coordinates is any bijection `e`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 28, proof of Theorem 6.1

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic

namespace SymBoolPCSP.Galois

open PCSPBLPAff.Symmetric

/-- Proof of Theorem 6.1, p. 28: for vectors `y_1, …, y_k ∈ D^m` (here `(y_i)_j = x j i`), the
promise relation `(S′_m, T′_m)` with `S′_m = {(f(y_1), …, f(y_k)) : f ∈ S_m}` and
`T′_m = {(f(y_1), …, f(y_k)) : f ∈ T_m}` is ppp-definable from the one-relation family
`{(S_m, T_m)}`, functions `D^m → D` being listed as vectors of their `|D|^m` values in the
order `e`. -/
theorem sprime_from_s {τ : Type} [Fintype τ] {ar : τ → ℕ} {D : Type} [Fintype D]
    [DecidableEq D] (𝔸 𝔹 : RelStruct τ ar D) (hΓ : IsPromiseFamily 𝔸 𝔹)
    {k m : ℕ} (x : Fin m → Fin k → D) (e : Fin (Fintype.card (Fin m → D)) ≃ (Fin m → D)) :
    PPPDefinable (single (asTuples e (SL 𝔸 m))) (single (asTuples e (TL 𝔸 𝔹 m)))
      (evalAt x (SL 𝔸 m)) (evalAt x (TL 𝔸 𝔹 m)) := by sorry

end SymBoolPCSP.Galois
