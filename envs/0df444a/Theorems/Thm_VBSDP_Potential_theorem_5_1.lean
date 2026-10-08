-- Prove2me | Theorems.Thm_VBSDP_Potential_theorem_5_1
-- name    : VBSDP.Potential.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:26:11.486686+00:00
-- url     : https://prove2.me/theorems/8bbc6b23-f54a-41e0-a2ef-d2e87b307c2d
-- title:
--   Theorem 5.1 — fixed potential decrease gives a duality-gap bound
-- statement:
--   Consider the primal semidefinite program defined by symmetric $F_0,\ldots,F_m$, with linearly independent $F_1,\ldots,F_m$, matrix size $n\ge1$, and the potential parameter $\nu\ge1$. Fix $k\in\mathbb N$ and let $(x^{(j)},Z^{(j)})$, $j=0,\ldots,k$, be strictly feasible primal-dual pairs. Suppose a fixed $\delta>0$ satisfies $\varphi(x^{(j+1)},Z^{(j+1)})\le\varphi(x^{(j)},Z^{(j)})-\delta$ at every step $j<k$. For $0<\varepsilon<1$, if
--
--   $$k\ge\frac{\nu\sqrt n\log(1/\varepsilon)+\psi(x^{(0)},Z^{(0)})}{\delta},$$
--
--   then the duality gap obeys
--
--   $$\operatorname{Tr}(F(x^{(k)})Z^{(k)})\le\varepsilon\operatorname{Tr}(F(x^{(0)})Z^{(0)}).$$
--
--   This gives a numerical iteration bound whenever a method guarantees a fixed decrease in the potential.
--
--   **Formalization Note** The paper prints a strict “<” conclusion, but equality is possible at the displayed threshold. For $n=m=1$, $F_0=0$, $F_1=c=Z^{(j)}=1$, $x^{(j)}=e^{-j}$, $\nu=\delta=1$, and $\varepsilon=e^{-1}$, the bound holds with equality at $k=1$. The non-strict conclusion records the boundary-correct result. The step condition (56) and strict feasibility are required only for the iterates up to $k$, so the statement covers a method that stops after $k$ steps. Strict feasibility and $n\ge1$ protect all logarithms. The `Fin m` matrices are zero-based with $F_0$ separate.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 77 (PDF p. 29), (56) and Theorem 5.1; corrected strict sign as noted, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Potential_IsStrictlyFeasiblePair
import Definitions.Def_VBSDP_Potential_phi

namespace VBSDP.Potential

/-- Theorem 5.1 with the boundary-correct non-strict conclusion. -/
theorem theorem_5_1 {m n : ℕ} [NeZero n] (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (xs : ℕ → Fin m → ℝ) (Zs : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (hfeas : ∀ j ≤ k, IsStrictlyFeasiblePair c F₀ F (xs j) (Zs j))
    (δ : ℝ) (hδ : 0 < δ)
    (h56 : ∀ j < k, phi ν F₀ F (xs (j + 1)) (Zs (j + 1)) ≤
      phi ν F₀ F (xs j) (Zs j) - δ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hk : (ν * Real.sqrt n * Real.log (1 / ε) +
      psi F₀ F (xs 0) (Zs 0)) / δ ≤ k) :
    (VBSDP.Duality.lmi F₀ F (xs k) * Zs k).trace ≤
      ε * (VBSDP.Duality.lmi F₀ F (xs 0) * Zs 0).trace := by sorry

end VBSDP.Potential
