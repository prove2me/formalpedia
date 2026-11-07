-- Prove2me | Theorems.Thm_SysBathGibbs_proposition_4_5
-- name    : SysBathGibbs.proposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:34.753193+00:00
-- url     : https://prove2.me/theorems/00e01cbd-6e29-4d56-809a-b42f40c9e21c
-- title:
--   Proposition 4.5 — Site-matrix estimates and the uniform bound (4.12)
-- statement:
--   Let $\beta>0$, $\sigma=\beta/2$, and $H_n$ a chain as in (1.2).
--
--   1. For each $u_*>0$ and $m\in\mathbb N_0$ there are $C,c>0$, depending only on $\beta,q,u_*,m$, such that for every chain, every $x\in[n]$, $|u|\le u_*$, $r\ge0$ and $X_x\in\{M_x,Q_x,H_x,G_{D,x},B^{\mathrm{Lamb}}_x\}$,
--   $$
--   \|(\mathrm{ad}^m_{H_n}X_x)(-iu)\|_{\mathrm{op}}\le C,\qquad \|(\mathrm{id}-\mathcal E_{x,r})((\mathrm{ad}^m_{H_n}X_x)(-iu))\|_{\mathrm{op}}\le Ce^{-cr}.
--   $$
--   2. There is $C_\beta$, depending only on $\beta$ and $q$, such that for every chain and $x$,
--   $$
--   \sup_{T\ge0}\|\Gamma^{-1}\mathcal L_{x,T}\Gamma\|_{\rho_\beta\to\rho_\beta}+\|\Gamma^{-1}\mathcal L_x\Gamma\|_{\rho_\beta\to\rho_\beta}\le C_\beta\beta.
--   $$
--
--   The site matrices and their fixed-order commutators stay quasi-local under bounded imaginary-time evolution, and the site generators are bounded on relative densities uniformly in $n$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: induced norms and sup_{T≥0} in ℝ → values in [0, ∞]; reason: the supremum is meaningful without a separate boundedness proof; the bound makes it finite
--   - encoding: L_{x,T} at T = 0 → the empty window (0, 0), so L_{x,0} = 0; reason: the formula (3.8) at T = 0
--   - encoding: a chain [n] of qudits of dimension 2^q → q ≥ 1 as a hypothesis; reason: a qudit has q ≥ 1 qubits
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Proposition 4.5 (incl. eq. (4.12)), p.33

import Definitions.Def_SysBathGibbs_Generator

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Proposition 4.5 (Site-matrix estimates)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.33.
For fixed `u⋆ > 0`, `m ∈ ℕ₀` there are `C, c > 0` such that for all `x`, `|u| ≤ u⋆`, `r ≥ 0` and
`X_x ∈ {M_x, Q_x, H_x, G_{D,x}, B^Lamb_x}`: `‖(ad^m_{H_n} X_x)(-iu)‖_op ≤ C` and
`‖(id - E_{x,r})((ad^m_{H_n} X_x)(-iu))‖_op ≤ C e^{-cr}`. Moreover (4.12):
`sup_{T≥0} ‖Γ⁻¹L_{x,T}Γ‖ + ‖Γ⁻¹L_xΓ‖ ≤ C_β β`.

**Formalization Note.** `B^Lamb_x` is the uncentered form (3.25). At `T = 0` the window is empty and
`L_{x,0} = 0`. Norms in (4.12) are in `ℝ≥0∞`, where the `sup` over `T` is meaningful without a
boundedness proof. -/
theorem proposition_4_5 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      (∀ (uStar : ℝ) (m : ℕ), 0 < uStar →
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ (n : ℕ) (h : Fin (n - 1) → SysMat n q), IsChain h →
            ∀ (x : Fin n) (u r : ℝ), |u| ≤ uStar → 0 ≤ r →
              ∀ X ∈ ({siteM β h x Set.univ, siteQ β h x Set.univ, siteH β h x Set.univ,
                  siteGD β h x, siteLamb β h x} : Set (SysMat n q)),
                opNorm (evo (chainHam h) (-(Complex.I * u)) ((comm (chainHam h))^[m] X)) ≤ C ∧
                opNorm (evo (chainHam h) (-(Complex.I * u)) ((comm (chainHam h))^[m] X) -
                    traceAt x r (evo (chainHam h) (-(Complex.I * u)) ((comm (chainHam h))^[m] X))) ≤
                  C * Real.exp (-c * r)) ∧
      ∃ Cβ : ℝ, 0 < Cβ ∧
        ∀ (n : ℕ) (h : Fin (n - 1) → SysMat n q), IsChain h → ∀ x : Fin n,
          (⨆ T : {T : ℝ // 0 ≤ T},
              kmsOpNorm β (chainHam h) (onRelDens β (chainHam h) (siteGen β h x (finWin T.1)))) +
            kmsOpNorm β (chainHam h) (onRelDens β (chainHam h) (siteGen β h x Set.univ)) ≤
          ENNReal.ofReal (Cβ * β) := by sorry

end SysBathGibbs
