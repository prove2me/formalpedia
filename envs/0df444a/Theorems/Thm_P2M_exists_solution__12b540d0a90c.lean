-- Prove2me | Theorems.Thm_P2M_exists_solution__12b540d0a90c
-- name    : P2M_exists_solution__12b540d0a90c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:43.257224+00:00
-- url     : https://prove2.me/theorems/fdd34417-cf54-40c0-b507-089daa157121
-- title:
--   P2 M exists solution  12b540d0a90c: P2 M exists solution  12b540d0a90c
-- statement:
--   The P2 M exists solution  12b540d0a90c construction uses the P2 M exists solution  12b540d0a90c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/InductionStep.lean#L567-L590
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/InductionStep.lean#L567-L590

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.ClassGroup.Basic
public import Definitions.Def_FltRegular_CaseII_AuxLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_KummersLemma
public import Definitions.Def_FltRegular_CaseII_InductionStep
set_option autoImplicit false
@[expose] public section
public section
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type} {p : ℕ} [NeZero p] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}
local notation3 "π" => hζ.toInteger - 1
local notation3 "𝔭" => Ideal.span {π}
local notation3 "𝔦" η => Ideal.span {(x + y * η : 𝓞 K)}
local notation3 "𝔵" => Ideal.span {x}
local notation3 "𝔶" => Ideal.span {y}
local notation3 "𝔷" => Ideal.span {z}
variable {m : ℕ} (e : x ^ p + y ^ p = ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
variable (hy : ¬ hζ.toInteger - 1 ∣ y) (hz : ¬ hζ.toInteger - 1 ∣ z)
variable (η : nthRootsFinset p (1 : 𝓞 K))
local notation3 "𝔪" => gcd 𝔵 𝔶
variable [hpri : Fact p.Prime]
variable [IsCyclotomicExtension {p} ℚ K]
local notation "𝔠" => fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η
local notation "𝔷'" => zDivM hζ e hy
local notation "𝔞" => rootDivZetaSubOneDvdGcd hp hζ e hy
local notation "η₀" => zetaSubOneDvdRoot hp hζ e hy
local notation "𝔞₀" => aEtaZeroDvdPPow hp hζ e hy
variable [Fintype (ClassGroup (𝓞 K))] (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
local notation "α" => fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg
local notation "β" => fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg
local notation "ε" => fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg
include hp hreg e hy hz

theorem P2M_exists_solution__12b540d0a90c : ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
    ¬ π ∣ y' ∧ ¬ π ∣ z' ∧ x' ^ p + y' ^ p = ε₃ * (π ^ m * z') ^ p := by sorry

alias «exists_solution'» := P2M_exists_solution__12b540d0a90c
