-- Prove2me | Theorems.Thm_SLQSolv_Finite_proposition_5_1
-- name    : SLQSolv.Finite.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:20.84892+00:00
-- url     : https://prove2.me/theorems/833caf7a-8760-4b6b-9baa-e5b105403b8a
-- title:
--   Proposition 5.1, p. 2292 — finiteness, quadratic value, convexity: (i) ⇒ (ii) ⇒ (iii) ⇒ (iv) and (v) ⇒ (ii)
-- statement:
--   Let (H1)–(H2) hold and let $t\in[0,T)$. Consider the statements
--
--   1. (i) Problem (SLQ) is finite at $t$;
--   2. (ii) Problem (SLQ)$^0$ is finite at $t$;
--   3. (iii) there is a symmetric $P(t)\in\mathbb S^n$ with $V^0(t,x)=\langle P(t)x,x\rangle$ for all $x\in\mathbb R^n$ (5.1);
--   4. (iv) for every $x\in\mathbb R^n$ the map $u\mapsto J(t,x;u)$ is convex on $\mathcal U[t,T]$;
--   5. (v) $\mathcal P[t,T]\ne\emptyset$.
--
--   Then
--
--   $$
--   \text{(i)}\Rightarrow\text{(ii)}\Rightarrow\text{(iii)}\Rightarrow\text{(iv)},\qquad \text{(v)}\Rightarrow\text{(ii)}.
--   $$
--
--   Here $\mathcal P[t,T]$ is the set of absolutely continuous $P:[t,T]\to\mathbb S^n$ with $P(T)\le G$ and $\Lambda(s,P(\cdot))\ge0$ a.e. on $[t,T]$.
--
--   The proposition relates finiteness of the inhomogeneous and the homogeneous problems, the quadratic structure of $V^0$ and convexity of the cost, and gives a Lyapunov-type sufficient condition for finiteness.
--
--   **Formalization Note** The four implications are stated as one conjunction. (i) is about the inhomogeneous problem, (ii) and (iii) about Problem (SLQ)$^0$, and (iv) about the inhomogeneous cost $J$. Convexity is the inequality $J(t,x;\theta u+(1-\theta)v)\le\theta J(t,x;u)+(1-\theta)J(t,x;v)$ for admissible $u,v$ and $\theta\in[0,1]$. The equality in (iii) is an equality in $[-\infty,\infty)$. Membership in $\mathcal P[t,T]$ is witnessed by the pair $(P,\dot P)$.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Proposition 5.1, p. 2292

import Mathlib
import Definitions.Def_SLQSolv_Finite_PSet

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

theorem proposition_5_1 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (t : ℝ≥0) (ht : t < d.T) :
    (IsFiniteAtTime Bs d t → IsFiniteAtTime Bs d.hom t) ∧
    (IsFiniteAtTime Bs d.hom t → ∃ Pt : Matrix (Fin n) (Fin n) ℝ, Pt.IsSymm ∧
      ∀ x, V0 Bs d t x = (((Pt *ᵥ x) ⬝ᵥ x : ℝ) : EReal)) ∧
    ((∃ Pt : Matrix (Fin n) (Fin n) ℝ, Pt.IsSymm ∧
      ∀ x, V0 Bs d t x = (((Pt *ᵥ x) ⬝ᵥ x : ℝ) : EReal)) →
      ∀ (x : Fin n → ℝ) (u v : ℝ≥0 → Ω → Fin m → ℝ), Adm Bs d t u → Adm Bs d t v →
        ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
          J Bs d t x (fun s ω => θ • u s ω + (1 - θ) • v s ω)
            ≤ θ * J Bs d t x u + (1 - θ) * J Bs d t x v) ∧
    ((∃ P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, IsInPSet d t P Pdot) →
      IsFiniteAtTime Bs d.hom t) := by sorry

end SLQSolv.Finite
