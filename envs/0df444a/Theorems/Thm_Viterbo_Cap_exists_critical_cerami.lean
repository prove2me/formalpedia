-- Prove2me | Theorems.Thm_Viterbo_Cap_exists_critical_cerami
-- name    : Viterbo.Cap.exists_critical_cerami
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:49:22.265199+00:00
-- url     : https://prove2.me/theorems/e801a9ac-fcaf-402c-b11e-62612c5c9ebf
-- title:
--   Linking lemma under a Cerami condition — a critical point of Φ with a ≤ Φ ≤ b in finite dimension
-- statement:
--   Let $H$ be a finite-dimensional real inner product space, $l: H\to E\times F$ a continuous linear equivalence with $E$ finite-dimensional normed and $F$ a real inner product space, $\Phi:H\to\mathbb R$ a $C^\infty$ function, $e\in F$ with $\|e\|=1$, and $0<a\le b$, $\rho>0$, $\varepsilon>0$, $\rho<R$. Suppose
--   - $\Phi(l^{-1}(0,z))\ge 2a$ whenever $\|z\|=\rho$;
--   - $\Phi(l^{-1}(y,se))\le a/2$ whenever $0<s<\varepsilon$, and whenever $s>0$ and $\|(y,s)\|\ge R$ (product norm, the maximum of $\|y\|$ and $|s|$);
--   - $\Phi(l^{-1}(y,se))\le b$ whenever $s>0$ and $\|(y,s)\|<R$;
--   - (Cerami) there are $R_1$ and $c_1>0$ with $c_1\le(1+\|x\|)\,\|\nabla\Phi(x)\|$ for every $x$ with $a\le\Phi(x)\le b$ and $\|x\|\ge R_1$.
--
--   Then some $x\in H$ has $a\le\Phi(x)\le b$ and $\nabla\Phi(x)=0$. This is `OAI.FiniteLinking.exists_critical` with its global gradient bound outside a ball replaced by the Cerami condition on the strip $a\le\Phi\le b$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, a step in the proof of the capacity statement (Hofer–Zehnder argument, Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3)

import Mathlib

open scoped ContDiff

namespace Viterbo.Cap

theorem exists_critical_cerami {H : Type} {E : Type} {F : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (l : H ≃L[ℝ] E × F) {Φ : H → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {e : F} (he : ‖e‖ = 1) {a b ρ ε R : ℝ}
    (ha : 0 < a) (hba : a ≤ b) (hρ : 0 < ρ) (hε : 0 < ε) (hR : ρ < R)
    (hpos : ∀ z : F, ‖z‖ = ρ → 2 * a ≤ Φ (l.symm (0, z)))
    (hnear : ∀ (y : E) (s : ℝ), 0 < s → s < ε → Φ (l.symm (y, s • e)) ≤ a / 2)
    (hfar : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y, s)‖ → Φ (l.symm (y, s • e)) ≤ a / 2)
    (hupper : ∀ (y : E) (s : ℝ), 0 < s → ‖(y, s)‖ < R → Φ (l.symm (y, s • e)) ≤ b)
    (hcerami : ∃ R₁ c₁ : ℝ, 0 < c₁ ∧ ∀ x, a ≤ Φ x → Φ x ≤ b → R₁ ≤ ‖x‖ →
      c₁ ≤ (1 + ‖x‖) * ‖gradient Φ x‖) :
    ∃ x : H, a ≤ Φ x ∧ Φ x ≤ b ∧ gradient Φ x = 0 := by
  sorry

end Viterbo.Cap
