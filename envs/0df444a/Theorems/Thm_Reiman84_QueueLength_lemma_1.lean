-- Prove2me | Theorems.Thm_Reiman84_QueueLength_lemma_1
-- name    : Reiman84.QueueLength.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:48:50.880557+00:00
-- url     : https://prove2.me/theorems/69b04f5e-216c-463b-a4cd-148717cb0d3e
-- title:
--   Lemma 1 — the reflection mapping (ψ, φ) on C₊: existence, uniqueness, (18) and (19)
-- statement:
--   Let $P$ be a nonnegative $K\times K$ matrix with spectral radius strictly less than one, $C$ the space of continuous functions $x:[0,\infty)\to\mathbb R^K$ and $C_+$ the subset with $x(0)\in\mathbb R^K_+$. For each $x\in C_+$ there exists a unique pair $y,z\in C$ satisfying, for $j=1,\dots,K$,
--   $$z_j(t)=x_j(t)+y_j(t)-\sum_{i=1}^Kp_{ij}y_i(t),\quad t\ge0,\qquad(14)$$
--   $$z_j(t)\ge0,\quad t\ge0,\qquad(15)$$
--   $y_j$ is nondecreasing with $y_j(0)=0$ (16), and $y_j$ increases only at times $t$ where $z_j(t)=0$ (17). Writing $y=\psi(x)$, $z=\phi(x)$:
--
--   1. (18) the restrictions of $y$ and $z$ to $[0,T]$ depend only on the restriction of $x$ to $[0,T]$;
--   2. (19) $\psi$ and $\phi$ are continuous mappings $C_+\to C$.
--
--   $Z=\phi(\xi)$ is the limit process of Theorem 1, and (19) is what lets the continuous mapping theorem carry convergence of $\tilde\zeta^n$ over to $Z^n$.
--
--   **Formalization Note** The result is Theorem 1 of Harrison and Reiman (1981a), cited in this paper. The paper states it for the routing matrix of §2; the hypotheses "nonnegative, spectral radius $<1$" (as $P^m\to0$) are those of §2 and of Proposition 1. $C$ carries the topology of uniform convergence on compact subsets of $[0,\infty)$ (not stated on the page); (19) is stated as sequential continuity, which is equivalent since that topology is metrizable. Condition (17) is: $y_j$ is constant on every interval on which $z_j>0$.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 445, Lemma 1, Eqs. (14)–(19) (Harrison and Reiman 1981a, Theorem 1)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths

namespace Reiman84.QueueLength

open Filter Topology

/-- Lemma 1, p. 445 (Harrison and Reiman 1981a, Theorem 1), for a nonnegative `P` with spectral
radius strictly less than one (`Pᵐ → 0`):
* for each `x ∈ C_+` there is a unique pair `(y, z) = (ψ(x), φ(x))` of continuous paths on
  `[0, ∞)` satisfying (14)–(17);
* (18) the restrictions of `y` and `z` to `[0, T]` depend only on the restriction of `x` to
  `[0, T]`;
* (19) `ψ` and `φ` are continuous `C_+ → C` for uniform convergence on compacts. -/
theorem lemma_1 {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0)) :
    (∀ x : ℝ → Fin K → ℝ, IsCPlus x →
      ∃ y z, IsReflectionPair P x y z ∧
        ∀ y' z', IsReflectionPair P x y' z' → ∀ t, 0 ≤ t → y' t = y t ∧ z' t = z t) ∧
    (∀ (T : ℝ) (x y z x' y' z' : ℝ → Fin K → ℝ), IsReflectionPair P x y z →
      IsReflectionPair P x' y' z' → (∀ t ∈ Set.Icc (0 : ℝ) T, x t = x' t) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, y t = y' t ∧ z t = z' t) ∧
    (∀ (xs ys zs : ℕ → ℝ → Fin K → ℝ) (x y z : ℝ → Fin K → ℝ),
      (∀ n, IsReflectionPair P (xs n) (ys n) (zs n)) → IsReflectionPair P x y z →
      UocTendsto xs x → UocTendsto ys y ∧ UocTendsto zs z) := by sorry

end Reiman84.QueueLength
