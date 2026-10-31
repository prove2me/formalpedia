-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_linInterp_frame
-- name    : QAlgorithms.Nannicini.adiabatic_linInterp_frame
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-30T14:19:56.018787+00:00
-- url     : https://prove2.me/theorems/9f72bbc1-7756-4786-9973-6663d9ba2fd6
-- title:
--   Smooth eigenvector frame and reduced-resolvent vector for a gapped linear interpolation
-- statement:
--   There is a universal constant $K$ such that the following holds. Let $H_I,H_F$ be Hermitian, $H(s)=(1-s)H_I+sH_F$, $D=H_F-H_I$, and let $\lambda:[0,1]\to\mathbb R$ be continuous with $\lambda(s)$ a simple eigenvalue of $H(s)$ separated by at least $\gamma>0$ from the rest of the spectrum for every $s\in[0,1]$. Let $\varphi_0$ be a unit eigenvector of $H(0)$ for $\lambda(0)$. Then there are functions $u,u',v,v'$ with $u(0)=\varphi_0$ such that for all $s\in[0,1]$: $u$ and $v$ have derivatives $u'(s)$, $v'(s)$ within $[0,1]$; $u(s)$ is a unit eigenvector of $H(s)$ with eigenvalue $\lambda(s)$; $(H(s)-\lambda(s))v(s)=u'(s)$; $\|v(s)\|\le K\|D\|/\gamma^2$ and $\|v'(s)\|\le K\|D\|^2/\gamma^3$ (operator norm). Proof idea: parallel transport $u'=-R(s)Du$ with $R(s)$ the reduced resolvent ($\|R\|\le1/\gamma$), $v=Ru'$; bound $R'$ via $P'=-RDP-PDR$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5, §9.2 (proof of Corollary 9.24); cf. Jansen–Ruskai–Seiler, J. Math. Phys. 48 (2007) 102111, and Kato, J. Phys. Soc. Japan 5 (1950). https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

universe u

namespace QAlgorithms.Nannicini

/-- Spectral input for the adiabatic theorem along `H(s) = (1 − s)H_I + sH_F`. If `λ(s)` is a
continuous simple eigenvalue of `H(s)` with gap `γ > 0` on `[0, 1]`, the eigenvector `φ₀` of
`H(0)` can be transported to a differentiable unit eigenvector family `u(s)` (eigenvalue `λ(s)`),
and `u′(s)` lies in the range of `H(s) − λ(s)`: `u′ = (H − λ)v` with `v` differentiable,
`‖v‖ ≤ K‖H_F − H_I‖/γ²`, `‖v′‖ ≤ K‖H_F − H_I‖²/γ³`, for a universal constant `K`. (One can take
`u′ = −R D u` (parallel transport) and `v = R u′`, `R` the reduced resolvent, `D = H_F − H_I`.) -/
theorem adiabatic_linInterp_frame : ∃ K : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (HI HF : Matrix ι ι ℂ), HI.IsHermitian → HF.IsHermitian →
    ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
    ∀ (φ0 : EuclideanSpace ℂ ι), IsState φ0 → act (linInterp HI HF 0) φ0 = (lam 0 : ℂ) • φ0 →
    ∀ (γ : ℝ), 0 < γ →
    (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
    ∃ u u' v v' : ℝ → EuclideanSpace ℂ ι, u 0 = φ0 ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt u (u' s) (Set.Icc 0 1) s ∧ HasDerivWithinAt v (v' s) (Set.Icc 0 1) s ∧
        IsState (u s) ∧ act (linInterp HI HF s) (u s) = (lam s : ℂ) • u s ∧
        act (linInterp HI HF s) (v s) - (lam s : ℂ) • v s = u' s ∧
        ‖v s‖ ≤ K * specNorm (HF - HI) / γ ^ 2 ∧
        ‖v' s‖ ≤ K * specNorm (HF - HI) ^ 2 / γ ^ 3 := by
  sorry

end QAlgorithms.Nannicini
