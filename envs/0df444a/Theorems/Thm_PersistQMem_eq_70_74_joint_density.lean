-- Prove2me | Theorems.Thm_PersistQMem_eq_70_74_joint_density
-- name    : PersistQMem.eq_70_74_joint_density
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:38.393072+00:00
-- url     : https://prove2.me/theorems/bd05344c-2328-47cb-bc87-3566dd2638cf
-- title:
--   §6.6, (70)–(74) — joint densities along measurable histories
-- statement:
--   Let $h\mapsto\mathcal E_h$ be a measurable adaptive instrument from parent histories $Y$ to next records $\mathcal X$ (input dimension $d\ge1$, memory embedded in $\mathbb C^K$), and let $\nu$ be a $\sigma$-finite base measure on $Y$. Then:
--
--   1. $\mu_h(S)=d^{-1}\operatorname{Tr}\Gamma_h(S)$ is a Markov kernel, and $\eta(A)=\int\mu_h(A_h)\,d\nu(h)$ is the product measure of (70);
--   2. there is a jointly measurable positive matrix density $J(h,a)$ with $\tilde\Gamma(A)=\int\Gamma_h(A_h)\,d\nu(h)=\int_AJ\,d\eta$ (71) for every measurable $A$ with $\eta(A)<\infty$;
--   3. $\int\operatorname{Tr}_{\mathrm{out}}J(h,a)\,d\mu_h(a)=I_d$ for $\nu$-almost every $h$ (72);
--   4. with $\Phi_{h,a}(Z)=\operatorname{Tr}_{\mathrm{in}}[(Z^{\mathsf T}\otimes I_K)J(h,a)]$, every positive measurable field $Z(h)$ with $\int\operatorname{Tr}Z(h)\,d\nu(h)<\infty$ satisfies
--   $$\int\mathcal E_h(A_h)(Z(h))\,d\nu(h)=\int_A\Phi_{h,a}(Z(h))\,d\eta(h,a)\tag{73}$$
--   for every measurable $A$;
--   5. there are $q=Kd$ jointly measurable Kraus fields $M_{h,a,l}$ with $\Phi_{h,a}(Z)=\sum_{l=1}^qM_{h,a,l}ZM_{h,a,l}^*$, dominated by $\nu(dh)\mu_h(da)\#(dl)$ (74).
--
--   Here $A_h=\{a:(h,a)\in A\}$. This is the bridge from instrument-valued kernels to the Kraus-density protocol model of Theorem 2.2.
--
--   Differences from the source:
--   - reading: “a base measure ν on parent histories” → ν σ-finite; reason: the construction applies the Radon–Nikodym theorem, which needs σ-finiteness; the paper uses it with ν = ν_t, built from probability kernels and finite counting measures
--   - reading: (71) for measurable A ⊆ Y × X → (71) for measurable A with η(A) < ∞, where Γ̃(A) is a finite matrix; reason: for η(A) = ∞ the entries of Γ̃(A) need not be finite
--   - encoding: matrix-valued integrals; Tr_out, Tr_in → entrywise Bochner integrals, each asserted integrable; the published partial traces over the right (output) and left (input) factor; reason: Lean convention
--   - encoding: the dominating measure ν(dh)μ_h(da)#(dl) of (74) → η with the finite Kraus index summed; reason: integrating against counting measure on a finite index set is the sum
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.6, (70)–(74), p.28 (PDF p.31)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_PersistQMem_CPInstrumentMeasure

open scoped Matrix ComplexOrder Kronecker
open MeasureTheory ProbabilityTheory

namespace PersistQMem

/-- **§6.6, (70)–(74), p.28: joint densities along measurable histories** (Tao, Shen, *Structural
Lower Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission,
manuscript of 2026-11-03, sha256 6d48ad24…, §6.6, (70)–(74), p.28). Let `h ↦ E_h` be a measurable
adaptive instrument from parent histories `Y` to next records `X` (input dimension `d ≥ 1`, memory
embedded in `C^K`) and `ν` a σ-finite base measure on `Y`. Then:
1. `μ_h(S) = d⁻¹ Tr Γ_h(S)` is a Markov kernel; `η = ν ⊗ μ` is the product measure of (70);
2. (71) there is a jointly measurable positive matrix density `J(h, a)` with
   `Γ̃(A) = ∫ Γ_h(A_h) dν(h) = ∫_A J dη` for every measurable `A ⊆ Y × X` with `η(A) < ∞`;
3. (72) `∫ Tr_out J(h, a) dμ_h(a) = I_d` for `ν`-almost every `h`;
4. (73) with `Φ_{h,a}(Z) = Tr_in[(Zᵀ ⊗ I_K) J(h, a)]`, every positive measurable field `Z(h)` with
   `∫ Tr Z(h) dν(h) < ∞` satisfies `∫ E_h(A_h)(Z(h)) dν(h) = ∫_A Φ_{h,a}(Z(h)) dη(h, a)` for every
   measurable `A`;
5. (74) there are `q = Kd` jointly measurable Kraus fields `M_{h,a,l}` with
   `Φ_{h,a}(Z) = Σ_{l=1}^q M_{h,a,l} Z M_{h,a,l}*`.

**Formalization Note.** `A_h = {a | (h, a) ∈ A}`. Choi matrices live on `C^d ⊗ C^K` (input ⊗
output, `choi`); `Tr_out` and `Tr_in` are the published partial traces over the right and left
factor. Matrix integrals are entrywise Bochner integrals, each asserted integrable. The dominating
measure `ν(dh) μ_h(da) #(dl)` of (74) is `η` together with the counting measure on the finite
Kraus index, which is the sum over `l`. -/
theorem eq_70_74_joint_density {Y X : Type} [MeasurableSpace Y] [MeasurableSpace X] {d K : ℕ}
    (hd : 1 ≤ d) (E : Y → CPInstrumentMeasure X d K) (hE : IsMeasurableAdaptive E)
    (ν : Measure Y) [SigmaFinite ν] :
    ∃ κ : Kernel Y X, IsMarkovKernel κ ∧
      (∀ h S, MeasurableSet S → κ h S = ENNReal.ofReal ((d : ℝ)⁻¹ * (choi ((E h).E S)).trace.re)) ∧
    ∃ J : Y × X → Matrix (Fin d × Fin K) (Fin d × Fin K) ℂ,
      (∀ q q', Measurable fun x => J x q q') ∧ (∀ x, (J x).PosSemidef) ∧
      -- (71)
      (∀ A : Set (Y × X), MeasurableSet A → (ν ⊗ₘ κ) A ≠ ⊤ → ∀ q q',
        Integrable (fun h => choi ((E h).E (Prod.mk h ⁻¹' A)) q q') ν ∧
        IntegrableOn (fun x => J x q q') A (ν ⊗ₘ κ) ∧
        ∫ h, choi ((E h).E (Prod.mk h ⁻¹' A)) q q' ∂ν = ∫ x in A, J x q q' ∂(ν ⊗ₘ κ)) ∧
      -- (72)
      (∀ᵐ h ∂ν, ∀ i i' : Fin d,
        Integrable (fun a => WildeQIT.partialTraceRight (J (h, a)) i i') (κ h) ∧
        ∫ a, WildeQIT.partialTraceRight (J (h, a)) i i' ∂(κ h) =
          (1 : Matrix (Fin d) (Fin d) ℂ) i i') ∧
      -- (73)
      (∀ Z : Y → Matrix (Fin d) (Fin d) ℂ, (∀ h, (Z h).PosSemidef) →
        (∀ i i', Measurable fun h => Z h i i') → Integrable (fun h => (Z h).trace.re) ν →
        ∀ A : Set (Y × X), MeasurableSet A → ∀ o o' : Fin K,
          Integrable (fun h => (E h).E (Prod.mk h ⁻¹' A) (Z h) o o') ν ∧
          IntegrableOn (fun x => WildeQIT.partialTraceLeft
            (((Z x.1)ᵀ ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) * J x) o o') A (ν ⊗ₘ κ) ∧
          ∫ h, (E h).E (Prod.mk h ⁻¹' A) (Z h) o o' ∂ν =
            ∫ x in A, WildeQIT.partialTraceLeft
              (((Z x.1)ᵀ ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) * J x) o o' ∂(ν ⊗ₘ κ)) ∧
      -- (74)
      ∃ Mk : Y × X → Fin (K * d) → Matrix (Fin K) (Fin d) ℂ,
        (∀ l o c, Measurable fun x => Mk x l o c) ∧
        ∀ x (Z : Matrix (Fin d) (Fin d) ℂ),
          WildeQIT.partialTraceLeft ((Zᵀ ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) * J x) =
            ∑ l, Mk x l * Z * (Mk x l)ᴴ := by sorry

end PersistQMem
