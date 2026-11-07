-- Prove2me | Theorems.Thm_PRUPermLayer_lemma_4_1
-- name    : PRUPermLayer.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:40.561752+00:00
-- url     : https://prove2.me/theorems/1ca29940-0ac6-4b42-9cde-045ff8fdfc74
-- title:
--   Lemma 4.1 — pair bound $\mathbb E_L\mathrm{Tr}((\Pi^{\mathrm{eq}}_{ij}\otimes I)L^{\otimes t}\rho(L^\dagger)^{\otimes t}) \le \delta_{\mathrm{eq}}(\mu)^n$
-- statement:
--   Let $\mu$ be a distribution on $U(2)$ and $L \sim \mu^{\otimes n}$. Let $\rho$ be a state on $t$ registers of $n$ qubits and a reference register, and let $1 \le i < j \le t$. Then
--   $$
--   \mathop{\mathbb E}_{L\sim\mu^{\otimes n}} \mathrm{Tr}\Big((\Pi^{\mathrm{eq}}_{ij}\otimes I)\, L^{\otimes t}\rho\,(L^\dagger)^{\otimes t}\Big) \le \delta_{\mathrm{eq}}(\mu)^n ,
--   $$
--   where $\Pi^{\mathrm{eq}}_{ij}$ is the equality projector on registers $i$ and $j$.
--
--   No input state, entangled or not, makes two registers collide with probability above $\delta_{\mathrm{eq}}(\mu)^n$ after the layer, for every single-qubit law $\mu$.
--
--   Differences from the source:
--   - encoding: registers $1,\dots,t$ and a reference register → registers $0,\dots,t-1$ and a reference register of any finite type $R$; reason: Lean indexing; same statement
--   - encoding: $\mathrm{Tr}(\cdot)$ and a distribution $\mu$ on $U(2)$ → real part of the trace; a Borel probability measure on $U(2)$; reason: the trace is real; same objects
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 4.1, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_PRUPermLayer_layerLaw
import Definitions.Def_PRUPermLayer_piEqPair
import Definitions.Def_PRUPermLayer_deltaEq
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Lemma 4.1** (pair bound; Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 4.1, p.17 (PDF p.19)). Let `µ` be a distribution on `U(2)`, let `ρ` be a state on `t` registers of `n` qubits and a reference register, and let `1 ≤ i < j ≤ t`. Then `E_{L∼µ^{⊗n}} Tr((Π^eq_{ij} ⊗ I) L^{⊗t} ρ (L†)^{⊗t}) ≤ δ_eq(µ)ⁿ`, where `Π^eq_{ij}` is the equality projector on registers `i` and `j`.

**Formalization Note** `L ∼ µ^{⊗n}` is `layerLaw µ n`; `L^{⊗t}` and `(L†)^{⊗t}` are the
published `tensorPow` of `L` and of `star L`, acting on the `t` registers (`Fin t → Fin (2 ^ n)`,
register `i : Fin t` being the source's register `i + 1`) and as the identity on the reference
register `R`, any finite type. The trace is real; its real part is integrated. -/
theorem lemma_4_1 (μ : Measure (Matrix.unitaryGroup Bool ℂ)) [IsProbabilityMeasure μ] (n t : ℕ)
    {R : Type*} [Fintype R] [DecidableEq R]
    (ρ : Matrix ((Fin t → Fin (2 ^ n)) × R) ((Fin t → Fin (2 ^ n)) × R) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ)
    (i j : Fin t) (hij : i < j) :
    ∫ L, ((Matrix.kroneckerMap (· * ·) (piEqPair (2 ^ n) t i j) (1 : Matrix R R ℂ) *
        Matrix.kroneckerMap (· * ·)
          (ShadowTomography.UpperBound.tensorPow (L : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) t)
          (1 : Matrix R R ℂ) * ρ *
        Matrix.kroneckerMap (· * ·)
          (ShadowTomography.UpperBound.tensorPow (star (L : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) t)
          (1 : Matrix R R ℂ)).trace.re) ∂(layerLaw μ n) ≤ deltaEq μ ^ n := by sorry

end PRUPermLayer
