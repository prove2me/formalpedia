-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_4_15
-- name    : SunGroupIso.Class2.lemma_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:58.300327+00:00
-- url     : https://prove2.me/theorems/4a60220c-4495-4ea4-8bae-36bc4c9f40d7
-- title:
--   Lemma 4.15 — the group restriction construction algorithm
-- statement:
--   For all fixed hypothesis constants $c_0,c_1$, there are one Turing machine $M$ and constants $A,C$, chosen before the prime and every input, with: for every prime $p$, every labelled $p$-group $G$ of class 2 of order $p^n$, positive integers $\delta,\tau$ with $\tau\ge\delta+2$, every $d\le(n+1)^{c_0}$ and every $\lambda:D_{p^\delta}(G)\to(\mathbb Z/p^\delta)^d$ satisfying the second condition of Lemma 4.14 with constant $c_1$, writing $B=n/\delta+n\delta/\tau+\delta^3n^{4/9}(\log p)^2$ and $K=\lceil p^{CnB}\rceil$: $M$, on the Cayley table, $\delta$, $\tau$, $d$ and $\lambda$, outputs within $K$ steps a nonempty list of at most $K$ group restrictions of $G$, each with $\rho$ obtained from $\lambda$ ($\rho(h)=\lambda(h)p^{\tau-\delta}$) and $\zeta,\gamma\le AB$, which contains every group restriction of $G$ with $\rho$ obtained from $\lambda$ and $\zeta,\gamma\le AB$.
--
--   Differences from the source:
--   - encoding: an algorithm, no machine model fixed; inputs are groups, restrictions, tensors or matrix tuples → one Mathlib multi-stack Turing machine run through the published HMBinPacking.OutputsWithin, on binary codes built from the published encodeNat (groups by labelled Cayley tables, every labelling quantified); reason: Turing machines and RAMs simulate each other with polynomial overhead; any standard code differs polynomially
--   - reading: d = poly(n), condition 2 of Lemma 4.14, and enumeration with ζ, γ = O(B) → ∀ c₀ c₁, ∃ M A C, ∀ inputs; cutoff A·B and count/time ⌈p^(C·n·B)⌉; reason: the algorithm enumerates up to a fixed cutoff; the constants of the hypothesis are fixed first, and the independent O-bounds need not have the same coefficient; neither M nor A,C depend on p or an individual input
--   - reading: outputs all restrictions and the proof’s existence claim (PDF 26) → a nonempty exhaustive list at the cutoff A·B; reason: preserves both completeness and the existence used in Lemma 4.16; the missing hypotheses are recorded in I2
--   - encoding: ρ obtained from λ by extending to the proper domain (restricted to H = F) → r.ρ = extLabel p δ τ λ as a function on G; reason: only the values on F are used or coded
--   - encoding: real-valued bounds p^{x} → ⌈p^x⌉ in ℕ (ppow), natural logarithms; reason: step counts are natural numbers; rounding up changes no bound
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.15, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Restriction

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 4.15** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.15, p. 24, PDF p. 26). For a `p`-group `G` of class 2 of order `p^n`,
positive integers `δ, τ` with `τ ≥ δ + 2`, and `λ : D_{p^δ}(G) → (Z/p^δZ)^d`, `d = poly(n)`, satisfying the
second condition of Lemma 4.14, the group restriction construction algorithm outputs all the group
restrictions `(z, Y, g, H, ρ)` of `G` with `ζ, γ = O(n/δ + nδ/τ + δ^3 n^{4/9}(log p)^2)` and `ρ` obtained from
`λ` (`ρ(h) = λ(h) p^{τ−δ}`); it outputs at least one; its running time and the number of restrictions it
returns are `p^{O(n·(n/δ + nδ/τ + δ^3 n^{4/9}(log p)^2))}`. The `poly(n)` exponent `c₀` and the `O`-constant
`c₁` of the hypothesis are fixed before the constant `C` of the conclusion; the enumeration cutoff has its own constant `A`, and the machine may depend
on these fixed hypothesis constants. -/
theorem lemma_4_15 :
    ∀ c₀ c₁ : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ A C : ℕ,
      ∀ (p n N : ℕ) (G : Type) [Group G] [Finite G] (e : G ≃ Fin N) (δ τ d : ℕ)
        (lam : G → Fin d → ZMod (p ^ δ)),
        p.Prime → IsPGroupClass2 p G → Nat.card G = p ^ n → 0 < δ → δ + 2 ≤ τ →
        d ≤ (n + 1) ^ c₀ →
        (∃ J : Subgroup G, J ≤ Dsub p δ G ∧ Subgroup.center G ≤ J ∧
          (∃ S : List G, (S.length : ℝ) ≤ c₁ * (δ : ℝ) ^ 2 * (n : ℝ) ^ ((4 : ℝ) / 9) * Real.log p ^ 2 ∧
            (∀ x ∈ S, x ∈ Dsub p δ G) ∧ Subgroup.closure ((J : Set G) ∪ {x | x ∈ S}) = Dsub p δ G) ∧
          (∃ S : List G, (S.length : ℝ) ≤ c₁ * (δ : ℝ) ^ 2 * (n : ℝ) ^ ((4 : ℝ) / 9) * Real.log p ^ 2 ∧
            Subgroup.closure {x | x ∈ S} =
              Subgroup.closure {c | ∃ g ∈ Dsub p δ G, lam g = 0 ∧ ∃ j ∈ J, c = ⁅g, j⁆})) →
        let B : ℝ := (n : ℝ) / δ + (n : ℝ) * δ / τ + (δ : ℝ) ^ 3 * (n : ℝ) ^ ((4 : ℝ) / 9) * Real.log p ^ 2
        let K : ℕ := ppow p (C * n * B)
        let inp : List Bool := encGroup e ++ encUnary δ ++ encUnary τ ++ encodeNat d ++ encLabel e p δ lam
        ∃ L : List (Σ ζ γ : ℕ, Restriction G p ζ γ d τ),
          L ≠ [] ∧
          (∀ (ζ γ : ℕ) (r : Restriction G p ζ γ d τ), ⟨ζ, γ, r⟩ ∈ L →
            IsRestriction p δ r ∧ r.ρ = extLabel p δ τ lam ∧ (ζ : ℝ) ≤ A * B ∧ (γ : ℝ) ≤ A * B) ∧
          (∀ ζ γ (r : Restriction G p ζ γ d τ), IsRestriction p δ r → r.ρ = extLabel p δ τ lam →
            (ζ : ℝ) ≤ A * B → (γ : ℝ) ≤ A * B → ⟨ζ, γ, r⟩ ∈ L) ∧
          L.length ≤ K ∧
          HMBinPacking.OutputsWithin M inp (encList (fun x => encRestriction e δ x.2.2) L)
            (K) := by sorry

end SunGroupIso.Class2
