-- Prove2me | Theorems.Thm_PRUPermLayer_eq_11
-- name    : PRUPermLayer.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:36.994567+00:00
-- url     : https://prove2.me/theorems/05822699-a7e2-45e8-853b-5dc6f4ab7783
-- title:
--   Eq. (11) — $\mathbb E_L\mathrm{Tr}((I-\Pi_{\mathrm{Dist}})L^{\otimes t}\rho(L^\dagger)^{\otimes t}) \le \binom t2\delta_{\mathrm{eq}}(\mu)^n$
-- statement:
--   Let $\mu$ be a distribution on $U(2)$, $L \sim \mu^{\otimes n}$, and $\rho$ a state on $t$ registers of $n$ qubits and a reference register. Then
--   $$
--   \mathop{\mathbb E}_{L} \mathrm{Tr}\Big((I - \Pi_{\mathrm{Dist}})\, L^{\otimes t}\rho\,(L^\dagger)^{\otimes t}\Big) \le \binom t2\, \delta_{\mathrm{eq}}(\mu)^n .
--   $$
--
--   This is the distinctness half of the DNP concentration of the layer.
--
--   Differences from the source:
--   - encoding: registers $1,\dots,t$ and a reference register → registers $0,\dots,t-1$ and a reference register of any finite type $R$; reason: Lean indexing; same statement
--   - reading: $\rho$ in (11) (the state of Lemma 4.1, whose proof (11) completes) → $\rho$ a state on the $t$ registers and a reference register of any finite type; reason: (11) is derived from Lemma 4.1 for the same $\rho$; the case without reference is $R$ a one-point type
--   - encoding: $\mathrm{Tr}(\cdot)$ and a distribution $\mu$ on $U(2)$ → real part of the trace; a Borel probability measure on $U(2)$; reason: the trace is real; same objects
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §4.1, Eq. (11), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_PRUPermLayer_layerLaw
import Definitions.Def_PRUPermLayer_projMat
import Definitions.Def_PRUPermLayer_distSub
import Definitions.Def_PRUPermLayer_deltaEq
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Eq. (11)** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §4.1, display (11), p.17 (PDF p.19)). For a distribution `µ` on `U(2)` and a state `ρ` on `t` registers of `n` qubits and a reference register, `E_L Tr((I − Π_Dist) L^{⊗t} ρ (L†)^{⊗t}) ≤ C(t, 2) δ_eq(µ)ⁿ`, with `L ∼ µ^{⊗n}`.

**Formalization Note** `L ∼ µ^{⊗n}` is `layerLaw µ n`; `L^{⊗t}` and `(L†)^{⊗t}` are the
published `tensorPow` of `L` and of `star L`, acting on the `t` registers (`Fin t → Fin (2 ^ n)`,
register `i : Fin t` being the source's register `i + 1`) and as the identity on the reference
register `R`, any finite type. The trace is real; its real part is integrated. -/
theorem eq_11 (μ : Measure (Matrix.unitaryGroup Bool ℂ)) [IsProbabilityMeasure μ] (n t : ℕ)
    {R : Type*} [Fintype R] [DecidableEq R]
    (ρ : Matrix ((Fin t → Fin (2 ^ n)) × R) ((Fin t → Fin (2 ^ n)) × R) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ∫ L, ((Matrix.kroneckerMap (· * ·) (1 - projMat (distSub (2 ^ n) t)) (1 : Matrix R R ℂ) *
        Matrix.kroneckerMap (· * ·)
          (ShadowTomography.UpperBound.tensorPow (L : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) t)
          (1 : Matrix R R ℂ) * ρ *
        Matrix.kroneckerMap (· * ·)
          (ShadowTomography.UpperBound.tensorPow (star (L : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) t)
          (1 : Matrix R R ℂ)).trace.re) ∂(layerLaw μ n) ≤ (t.choose 2 : ℝ) * deltaEq μ ^ n := by sorry

end PRUPermLayer
