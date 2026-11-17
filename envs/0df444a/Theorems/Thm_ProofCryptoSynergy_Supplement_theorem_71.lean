-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_71
-- name    : ProofCryptoSynergy.Supplement.theorem_71
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:56:26.435399+00:00
-- url     : https://prove2.me/theorems/c9af63b1-c2f7-43f1-b2fd-7b2acdefcff3
-- title:
--   Theorem 71 — half-Levin NP-hardness of Total-Learn ⟺ full-support WE ⟺ publicly verifiable WE
-- statement:
--   The following are equivalent:
--
--   1. **(half-Levin NP-hardness of Total-Learn)** there exist a polynomial $s$ and a pair of machines $(f,g)$ such that for all polynomial $G$ and $\varepsilon^{-1}$, $(f,g)$ is an honest deterministic half-Levin reduction from SAT to $\mathrm{Total\text{-}Learn}_{G,\varepsilon}[s]$;
--   2. full-support witness encryption exists;
--   3. publicly verifiable witness encryption exists.
--
--   It characterizes a strong form of witness encryption by the NP-hardness of a learning problem.
--
--   Differences from the source:
--   - encoding: three-way equivalence → (1 ↔ 2) ∧ (2 ↔ 3); reason: a closed chain of equivalences
--   - reading: witness encryption (Section 6, unqualified) → polynomially secure WE for SAT (IsPolyWE); reason: Section 6 is the polynomial regime; every WE there is for SAT
--   - reading: a pair (tuple) of machines; no time bound printed → polynomial-time machines (UnifPoly), timed on all inputs and fixed before G, ε⁻¹; reason: Lemma 75 runs f inside a polynomial-time Enc and Lemma 76 builds polynomial-time f, g; one machine must serve every G
--   - encoding: honest: |f(x)| ≥ |x|^δ → length of the description MCircuit.code of the output sampler ≥ |x|^δ; reason: |f(x)| is the length of f’s output
--   - encoding: polynomial p(n) = n^c, c ≥ 1, with parameters s, g, ε⁻¹ : ℕ → ℕ → IsPolyFn: n ↦ ⌊n^c⌋, real c ≥ 1; reason: Definitions 21–27 take the parameters ℕ-valued; circuit sizes are naturals, so the floor changes no bound
--   - encoding: Pr < 1/2 + ε(n) → (Pr − 1/2)·ε⁻¹(n) < 1, the parameter being ε⁻¹ : ℕ → ℕ; reason: Definition 21 takes ε⁻¹ as the parameter; no division, and ε⁻¹(n) = 0 (ε undefined) is not the hardest case
--   - encoding: promise problems over strings (Definition 3); SAT with witness relation φ(w) = 1 → witness relations on sampling circuits and circuits, R_N containing the invalid instances; SAT witnesses with |w| ≤ |φ|; reason: N is exactly the set of no-instances; every variable index of φ is below |φ|, so SAT’s Y and N are unchanged
--   - encoding: a poly(n)-size circuit E sampling (x, b) → every output of the reduction has description length at most (n+2)^c, n its input length, for one constant c (PolySizeOut / RandPolySizeOut); reason: “poly(n)-size” names no polynomial, so one polynomial per reduction; n + 2 avoids the zero bound at n = 0
--   - reading: for all polynomial G, ε⁻¹, (f, g) is a half-Levin reduction to Total-Learn (on every input) → every f(φ) is a Total-Learn instance; yes-instances and witnesses are mapped for every φ; for each G, ε⁻¹, unsatisfiable φ are mapped to no-instances for all sufficiently long φ; reason: read for every φ, the no-condition forces perfectly balanced labels on every unsatisfiable φ (G(s(n)), ε⁻¹(n) are unbounded over polynomials at each fixed n ≥ 2), which gives NP = coNP; Lemma 76’s reduction is correct only for large n (Definition 13)
--   - encoding: {(x, ct) | ct ∈ range(Enc(x,−;−))} ∈ P → one polynomial-time machine outputs the membership bit on the pair (x, ct) (PubVerifiableWE); reason: the definition of P on the base's tuple encoding
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 71, p.53 (PDF 55)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
import Definitions.Def_ProofCryptoSynergy_Supplement_CGL
import Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyWE

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 71** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.53 (PDF 55)). The following are equivalent.
* (half-Levin NP-hardness of Total-Learn) There exist a polynomial `s` and a pair of machines `(f, g)` such
  that, for all polynomial `G`, `ε⁻¹`, `(f, g)` is an honest deterministic half-Levin reduction from SAT to
  `Total-Learn_{G,ε}[s]`;
* full-support witness encryption exists;
* publicly verifiable witness encryption exists.

**Formalization Note** The three-way equivalence is stated as `(1 ↔ 2) ∧ (2 ↔ 3)`. Section 6 is the
polynomial regime: witness encryption is the polynomially secure `IsPolyWE` for SAT. The machines are fixed
before `G`, `ε⁻¹` and run in polynomial time in their input length (`UnifPoly`); the theorem prints no time
bound. "`f` maps instances to instances" (Definition 4): every `f(φ)` is a Total-Learn instance (a sampler
whose first coordinate has full support) of polynomial size in its input length (`PolySizeOut`,
Definition 23: "a poly(n)-size circuit"). For each polynomial `G`, `ε⁻¹`, unsatisfiable formulas are mapped
to no-instances for all sufficiently long `φ` (the threshold may depend on `G`, `ε⁻¹`); yes-instances and
witnesses are mapped for every `φ`. Read for every `φ`, the no-condition would force, at each fixed input
length `n ≥ 2` of `f(φ)` (where `G(s(n))` and `ε⁻¹(n)` are unbounded over polynomials), perfectly balanced
labels on every unsatisfiable `φ`, which gives short certificates of unsatisfiability (`NP = coNP`); the
proof (Lemma 76, via Definition 13's "sufficiently large `n`") gives the asymptotic form. -/
theorem theorem_71 :
    (((∃ s : ℕ → ℕ, IsPolyFn s ∧ ∃ (f : List Bool → Samp) (gw : List Bool → List Bool → Wit),
        UnifPoly f gw ∧ Honest f ∧ PolySizeOut f ∧ (∀ x, (f x).WF ∧ (f x).FullSupp) ∧
        ∀ G εinv : ℕ → ℕ, IsPolyFn G → IsPolyFn εinv →
          (∀ x ∈ SATRel.Yes, f x ∈ (TotalLearn s G εinv).Yes) ∧
          (∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n → x ∈ SATRel.No →
            f x ∈ (TotalLearn s G εinv).No) ∧
          WitnessMap SATRel (TotalLearn s G εinv) f gw) ↔
      ∃ E : WEForSAT, IsPolyWE E ∧ FullSupportWE E) ∧
    ((∃ E : WEForSAT, IsPolyWE E ∧ FullSupportWE E) ↔
      ∃ E : WEForSAT, IsPolyWE E ∧ PubVerifiableWE E)) := by sorry

end ProofCryptoSynergy.Supplement
