-- Prove2me | Theorems.Thm_TrDegJac_theorem_4_12
-- name    : TrDegJac.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:25.224722+00:00
-- url     : https://prove2.me/theorems/4427e9f2-6508-4942-a048-3eff3c6a33b0
-- title:
--   Theorem 4.12 — $\operatorname{tr-deg}(f)-\lfloor\log_p D(g)\rfloor\le\operatorname{rank}_{\mathbb F(x)}\mathrm{Jac}(f)\le\operatorname{tr-deg}(f)$
-- statement:
--   Let $\mathbb F$ be a field of characteristic $p>0$, let $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$, and let $g=(f_i)_{i\in S}$ be any maximally algebraically independent subfamily of $f$ (maximal under inclusion). Write $D(g)=\prod_{i\in S}\deg f_i$ for its degree product. Then
--   $$
--   \operatorname{tr-deg}_{\mathbb F}(f)-\big\lfloor\log_p D(g)\big\rfloor\ \le\ \operatorname{rank}_{\mathbb F(x)}\mathrm{Jac}_x(f)\ \le\ \operatorname{tr-deg}_{\mathbb F}(f).
--   $$
--
--   In positive characteristic the Jacobian rank can fall below the transcendence degree ($x^p$ has zero Jacobian); the theorem bounds the loss by $\lfloor\log_p D(g)\rfloor$. For polynomials of degree at most $d$ it gives $(1-\log_p d)\operatorname{tr-deg}(f)\le\operatorname{rank}\mathrm{Jac}(f)$ (Corollary 4.13), so the Jacobian is exact once $p>D(g)$.
--
--   **Formalization Note** $\deg$ is the total degree; $D(g)\ge1$ because algebraically independent polynomials are non-constant, and $\lfloor\log_p D(g)\rfloor$ is `Nat.log p`. The lower bound is an inequality of integers.
--
--   Differences from the source:
--   - generalization: f₁, …, f_n ∈ F[x₁, …, x_n] (as many polynomials as variables) → f₁, …, f_m ∈ F[x₁, …, x_n] for every m; reason: §1.2 states the bound for any family, and the proof uses n only as the number of variables; m = n is the printed theorem
--   - generalization: tr-deg_F(f) − ⌊log_p D(g)⌋ ≤ rank_{F(x)} Jac(f) → the same lower bound together with rank_{F(x)} Jac(f) ≤ tr-deg_F(f); reason: the upper clause is the §1.2 display (p.6) and Proposition 4.7 (p.27); the conjunction specializes to the printed theorem
--   - encoding: char F = p; {g₁, …, g_r} ⊆ f maximally independent; ⌊log_p D(g)⌋ → [CharP F p] with p prime; an index set S with IsMaxAlgIndep f S; Nat.log p (∏_{i∈S} totalDegree (f i)) in ℤ; reason: §1.2 has char F = p > 0; index sets and subsets agree; Nat.log p k = ⌊log_p k⌋ for k ≥ 1 and D(g) ≥ 1
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Theorem 4.12, p.29; display of §1.2, p.6; Proposition 4.7, p.27

import Mathlib
import Definitions.Def_TrDegJac_IsMaxAlgIndep
import Definitions.Def_TrDegJac_trDeg
import Definitions.Def_TrDegJac_jacobian

set_option autoImplicit false

namespace TrDegJac

/-- **Theorem 4.12 (Jacobian approximation of transcendence degree)** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.29:
"Let F be a field with char F = p, for any f₁, …, f_n ∈ F[x₁, …, x_n] and let {g₁, …, g_r} ⊆ f be
any maximally algebraically independent subset of f, then
tr-deg_F(f) − ⌊log_p D(g)⌋ ≤ rank_{F(x)} Jac(f), where D(g) = ∏_{i=1}^r deg g_i."
Together with the upper bound of the display in §1.2, p.6: "r − ⌊log_p(∏_{i=1}^r deg g_i)⌋ ≤
rank_{F(x)} Jac_x(f) ≤ r" (the upper bound is Proposition 4.7, p.27).

**Formalization Note.** `char F = p > 0` is `[CharP F p]` with `p` prime (§1.2, p.6). The family is
`f : Fin m → F[x₁, …, x_n]` for any `m` (printed: `m = n`), and `g` is the subfamily indexed by any
`S` maximal under inclusion among independent index sets (`IsMaxAlgIndep`), not only one of maximum
size. `deg` is `totalDegree` and `D(g) = ∏_{i ∈ S} deg f_i ≥ 1` (independent polynomials are
non-constant), so `⌊log_p D(g)⌋ = Nat.log p D(g)`. The lower bound is an inequality in `ℤ`. The rank is
`Matrix.rank` of the Jacobian over `F(x)`. -/
theorem theorem_4_12 {F : Type*} [Field F] (p : ℕ) [CharP F p] (hp : p.Prime) {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) F) (S : Finset (Fin m)) (hS : IsMaxAlgIndep f S) :
    (trDeg f : ℤ) - (Nat.log p (∏ i ∈ S, (f i).totalDegree) : ℤ) ≤ ((jacobian f).rank : ℤ) ∧
      (jacobian f).rank ≤ trDeg f := by sorry

end TrDegJac
