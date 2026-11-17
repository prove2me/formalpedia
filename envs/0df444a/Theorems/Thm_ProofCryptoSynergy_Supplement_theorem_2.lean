-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_2
-- name    : ProofCryptoSynergy.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:51:11.670714+00:00
-- url     : https://prove2.me/theorems/38d21f6e-f8f3-4a48-baa0-a7a8eabb0f71
-- title:
--   Theorem 2 (informal; formal Corollaries 60(2), 62, 66) — conditional non-Levin NP-hardness of Gap-ImpMCSP
-- statement:
--   Assume that a subexponentially secure indistinguishability obfuscator exists. Then:
--
--   1. **(randomized NP-hardness)** if there is no infinitely-often subexponentially optimal proof system, there is a polynomial $s'$ such that for all subexponential functions $g'$ and $(\varepsilon')^{-1}$, SAT has a randomized polynomial-time half-Levin reduction (error $1/100$) to $\mathrm{Gap}_{g',\varepsilon'}\text{-ImpMCSP}[s']$;
--   2. **(nonuniform NP-hardness)** if $\mathsf{coNP}\not\subseteq\bigcap_{c\ge1}\text{io-}\mathsf{NTIME}[2^{n^{1/c}}]$, there is a polynomial $s'$ such that for all subexponential $g'$, $(\varepsilon')^{-1}$, SAT has a P/poly half-Levin reduction to $\mathrm{Gap}_{g',\varepsilon'}\text{-ImpMCSP}[s']$;
--   3. **(non-Levin NP-hardness)** if $\mathsf{coNP}\not\subseteq\text{io-}\mathsf{NP}$, there is a polynomial $g$ such that for every polynomial $s$ and every $\varepsilon\le1/2$, SAT has neither a nonuniform subexponential-size nor a randomized subexponential-time (error $1/100$) Levin reduction to $\mathrm{Gap}_{g,\varepsilon}\text{-ImpMCSP}[s]$.
--
--   This is the paper's second headline result: implicit MCSP is NP-hard under half-Levin reductions, yet a polynomial-gap version cannot be NP-hard under Levin reductions.
--
--   Differences from the source:
--   - generalization: (items 1–2) NP-hard under a randomized / nonuniform polynomial-time many-one reduction (informal) → a half-Levin reduction (many-one plus witness mapping), as in Corollaries 60(2) and 62; reason: p.7 says the reduction is actually half-Levin and the formal corollaries state it so; a half-Levin reduction is in particular many-one
--   - reading: a subexponential-gap version of ImpMCSP; a polynomial-gap version → ∃ polynomial s′ ∀ subexponential g′, (ε′)⁻¹ (items 1–2); ∃ polynomial g ∀ polynomial s ∀ ε ≤ 1/2 (item 3); reason: the parameters of the formal versions Corollaries 60(2), 62, 66
--   - reading: assumption (2) weakened (items 2 and 3) → each item carries its own proof-complexity hypothesis; iO is shared; reason: the bullets of p.7 and the hypotheses of Corollaries 60, 62, 66
--   - encoding: polynomial p(n) = n^c, c ≥ 1, with parameters s, g, ε⁻¹ : ℕ → ℕ → IsPolyFn: n ↦ ⌊n^c⌋, real c ≥ 1; reason: Definitions 21–27 take the parameters ℕ-valued; circuit sizes are naturals, so the floor changes no bound
--   - encoding: Pr < 1/2 + ε(n) → (Pr − 1/2)·ε⁻¹(n) < 1, the parameter being ε⁻¹ : ℕ → ℕ; reason: Definition 21 takes ε⁻¹ as the parameter; no division, and ε⁻¹(n) = 0 (ε undefined) is not the hardest case
--   - encoding: promise problems over strings (Definition 3); SAT with witness relation φ(w) = 1 → witness relations on sampling circuits and circuits, R_N containing the invalid instances; SAT witnesses with |w| ≤ |φ|; reason: N is exactly the set of no-instances; every variable index of φ is below |φ|, so SAT’s Y and N are unchanged
--   - encoding: polynomial-time (runtime at most n^c) → step bound (n+2)^c in |φ|, c ∈ ℕ, on the published OracleTM; reason: the same class of bounds; avoids the zero bound at n = 0
--   - encoding: subexponential g′, (ε′)⁻¹ → g′, ε′⁻¹ : ℕ → ℕ with the published IsSubexp (eventual bound 2^{n^{1/c}} for each c); reason: the base mission’s reading of §2.1; no positivity is added, the problems are monotone
--   - encoding: P/poly reduction (circuits of polynomial size) → f, g computed by multi-output circuits of size ≤ (n+2)^c, one per length n = |φ|, reading padIn and writing unpadOut; reason: Definition 4’s nonuniform reductions with a polynomial bound
--   - reading: Definition 5, condition 1, for every x ∈ Y₁ (w free) → for every (x, w) ∈ R_Y; reason: w is bound by R_Y as in Definition 4’s witness mapping
--   - encoding: randomized reduction (ε unspecified) → error 1/100; reason: p.17: if ε is not specified, ε = 1/100
--   - encoding: a poly(n)-size circuit E sampling (x, b) → every output of the reduction has description length at most (n+2)^c, n its input length, for one constant c (PolySizeOut / RandPolySizeOut); reason: “poly(n)-size” names no polynomial, so one polynomial per reduction; n + 2 avoids the zero bound at n = 0
--   - encoding: ε ≤ 1/2 → ε⁻¹(n) ≥ 2 for all n; reason: the same condition on the parameter ε⁻¹
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 2, p.7 (PDF 9); formal versions Corollary 60 item 2, pp.47–48 (PDF 49–50), Corollary 62, p.48 (PDF 50), Corollary 66, p.52 (PDF 54)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_IsSubexp
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_InUTIME
import Definitions.Def_ProofCryptoSynergy_Supplement_CoNPNotIoSubexpNTIME
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
import Definitions.Def_ProofCryptoSynergy_Supplement_CGL
import Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 2** (informal; Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.7 (PDF 9)), stated at the strength of its formal versions
Corollary 60 item 2 (pp.47–48), Corollary 62 (p.48) and Corollary 66 (p.52). Assume a subexponentially
secure iO exists. Then
1. (randomized NP-hardness) if there is no infinitely-often subexponentially optimal proof system, there is
   a polynomial `s'` such that for all subexponential `g'`, `(ε')⁻¹`, SAT has a randomized polynomial-time
   half-Levin reduction (error `1/100`) to `Gap_{g',ε'}-ImpMCSP[s']`;
2. (nonuniform NP-hardness) if `coNP ⊄ ⋂_{c≥1} io-NTIME[2^{n^{1/c}}]`, there is a polynomial `s'` such that
   for all subexponential `g'`, `(ε')⁻¹`, SAT has a P/poly half-Levin reduction to `Gap_{g',ε'}-ImpMCSP[s']`;
3. (non-Levin NP-hardness) if `coNP ⊄ io-NP`, there is a polynomial `g` such that for every polynomial `s` and
   every `ε ≤ 1/2`, SAT has neither a nonuniform subexponential-size nor a randomized subexponential-time
   (error `1/100`) Levin reduction to `Gap_{g,ε}-ImpMCSP[s]`.

**Formalization Note** The informal "many-one" reductions of items 1–2 are the formal half-Levin ones
(p.7: "The many-one NP-hardness reduction in the theorem above is actually half-Levin"). The reduction may
depend on `g'`, `ε'`; `s'` may not. "Polynomial-time" is a step bound `(n+2)^c`; "P/poly" is circuit size
`(n+2)^c`; "subexponential" is the published `IsSubexp`. `ε ≤ 1/2` is `ε⁻¹(n) ≥ 2` for all `n`. The error
`1/100` is the paper's default (p.17). Every reduction outputs instances of polynomial size in their input
length (`PolySizeOut`, `RandPolySizeOut`; Definition 25: "a poly(n)-size circuit `E`"). -/
theorem theorem_2 :
    SubexpIOExists →
      (NoIoSubexpOptimalPPS → ∃ s : ℕ → ℕ, IsPolyFn s ∧ ∀ g εinv : ℕ → ℕ,
          IsSubexp (fun n => (g n : ℝ)) → IsSubexp (fun n => (εinv n : ℝ)) →
          ∃ (c : ℕ) (ρ : ℕ → ℕ) (f : List Bool → List Bool → Samp)
            (gw : List Bool → List Bool → List Bool → Wit),
            RandHalfLevin (GapImpMCSP s g εinv) (fun n => (n + 2) ^ c) (1 / 100) ρ f gw ∧
              RandPolySizeOut ρ f) ∧
      (CoNPNotIoSubexpNTIME → ∃ s : ℕ → ℕ, IsPolyFn s ∧ ∀ g εinv : ℕ → ℕ,
          IsSubexp (fun n => (g n : ℝ)) → IsSubexp (fun n => (εinv n : ℝ)) →
          ∃ (c : ℕ) (f : List Bool → Samp) (gw : List Bool → List Bool → Wit),
            NonuHalfLevin (GapImpMCSP s g εinv) (fun n => (n + 2) ^ c) f gw ∧ PolySizeOut f) ∧
      (CoNPNotIoNP → ∃ g : ℕ → ℕ, IsPolyFn g ∧ ∀ s εinv : ℕ → ℕ, IsPolyFn s → (∀ n, 2 ≤ εinv n) →
          (¬ ∃ (t : ℕ → ℕ) (f : List Bool → Samp) (gw : List Bool → List Bool → Wit)
              (h : List Bool → Wit → List Bool),
              IsSubexp (fun n => (t n : ℝ)) ∧ NonuLevin (GapImpMCSP s g εinv) t f gw h ∧ PolySizeOut f) ∧
          (¬ ∃ (t ρ ρ₂ : ℕ → ℕ) (f : List Bool → List Bool → Samp)
              (gw : List Bool → List Bool → List Bool → Wit)
              (h : List Bool → Wit → List Bool → List Bool → List Bool),
              IsSubexp (fun n => (t n : ℝ)) ∧
                RandLevin (GapImpMCSP s g εinv) t (1 / 100) ρ ρ₂ f gw h ∧ RandPolySizeOut ρ f)) := by sorry

end ProofCryptoSynergy.Supplement
