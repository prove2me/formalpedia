-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_74
-- name    : ProofCryptoSynergy.Supplement.theorem_74
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:58:15.435432+00:00
-- url     : https://prove2.me/theorems/4c551009-4573-4b2b-a179-6eb021b609e9
-- title:
--   Theorem 74 — privately verifiable WE gives half-Levin NP-hardness of Extension-Learn
-- statement:
--   If privately verifiable witness encryption exists, then there exist a polynomial $s$ and a pair of machines $(f,g)$ such that for all polynomial $G$ and $\varepsilon^{-1}$, $(f,g)$ is an honest deterministic half-Levin reduction from SAT to
--   $$\mathrm{Extension\text{-}Learn}_{G,\varepsilon}[s].$$
--
--   Only this direction is claimed.
--
--   Differences from the source:
--   - reading: witness encryption (Section 6, unqualified) → polynomially secure WE for SAT (IsPolyWE); reason: Section 6 is the polynomial regime; every WE there is for SAT
--   - reading: a pair (tuple) of machines; no time bound printed → polynomial-time machines (UnifPoly), timed on all inputs and fixed before G, ε⁻¹; reason: Lemma 75 runs f inside a polynomial-time Enc and Lemma 76 builds polynomial-time f, g; one machine must serve every G
--   - encoding: honest: |f(x)| ≥ |x|^δ → length of the description MCircuit.code of the output sampler ≥ |x|^δ; reason: |f(x)| is the length of f’s output
--   - encoding: polynomial p(n) = n^c, c ≥ 1, with parameters s, g, ε⁻¹ : ℕ → ℕ → IsPolyFn: n ↦ ⌊n^c⌋, real c ≥ 1; reason: Definitions 21–27 take the parameters ℕ-valued; circuit sizes are naturals, so the floor changes no bound
--   - encoding: Pr < 1/2 + ε(n) → (Pr − 1/2)·ε⁻¹(n) < 1, the parameter being ε⁻¹ : ℕ → ℕ; reason: Definition 21 takes ε⁻¹ as the parameter; no division, and ε⁻¹(n) = 0 (ε undefined) is not the hardest case
--   - encoding: promise problems over strings (Definition 3); SAT with witness relation φ(w) = 1 → witness relations on sampling circuits and circuits, R_N containing the invalid instances; SAT witnesses with |w| ≤ |φ|; reason: N is exactly the set of no-instances; every variable index of φ is below |φ|, so SAT’s Y and N are unchanged
--   - encoding: a poly(n)-size circuit E sampling (x, b) → every output of the reduction has description length at most (n+2)^c, n its input length, for one constant c (PolySizeOut / RandPolySizeOut); reason: “poly(n)-size” names no polynomial, so one polynomial per reduction; n + 2 avoids the zero bound at n = 0
--   - reading: Definition 69: witnesses w ∈ {0,1}^{poly(n)} with (x, w) ∈ R_L → satisfying assignments with |w| ≤ |x|; reason: the SAT relation of the mission; every satisfiable formula has such a witness
--   - reading: for all polynomial G, ε⁻¹, (f, g) is a half-Levin reduction to Extension-Learn (on every input) → every f(φ) is an Extension-Learn instance; yes-instances and witnesses are mapped for every φ; for each G, ε⁻¹, unsatisfiable φ are mapped to no-instances for all sufficiently long φ; reason: read for every φ, the no-condition forces perfectly balanced labels on every unsatisfiable φ (NP = coNP); Lemma 76’s reduction is correct only for large n (Definition 13)
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 74, p.53 (PDF 55)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
import Definitions.Def_ProofCryptoSynergy_Supplement_CGL
import Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyWE

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 74** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.53 (PDF 55)). The first item implies the second in the following.
* Privately verifiable witness encryption exists;
* (half-Levin NP-hardness of Extension-Learn) there exist a polynomial `s` and a pair of machines `(f, g)`
  such that, for all polynomial `G`, `ε⁻¹`, `(f, g)` is an honest deterministic half-Levin reduction from SAT
  to `Extension-Learn_{G,ε}[s]`.

**Formalization Note** One direction only, as printed. Witness encryption is the polynomially secure
`IsPolyWE` for SAT; the machines are fixed before `G`, `ε⁻¹` and run in polynomial time (`UnifPoly`).
Every `f(φ)` is an Extension-Learn instance of polynomial size in its input length (`PolySizeOut`,
Definition 73: "a poly(n)-size circuit"). For each polynomial `G`, `ε⁻¹`, unsatisfiable formulas are mapped
to no-instances for all sufficiently long `φ` (threshold depending on `G`, `ε⁻¹`); yes-instances and
witnesses are mapped for every `φ`. Read for every `φ`, the no-condition would force perfectly balanced
labels on unsatisfiable formulas (`NP = coNP`); the proof (Lemma 76) gives the asymptotic form. -/
theorem theorem_74 :
    (∃ E : WEForSAT, IsPolyWE E ∧ PrivVerifiableWE E) →
      ∃ s : ℕ → ℕ, IsPolyFn s ∧ ∃ (f : List Bool → Samp) (gw : List Bool → List Bool → Wit),
        UnifPoly f gw ∧ Honest f ∧ PolySizeOut f ∧ (∀ x, (f x).WF) ∧
        ∀ G εinv : ℕ → ℕ, IsPolyFn G → IsPolyFn εinv →
          (∀ x ∈ SATRel.Yes, f x ∈ (ExtensionLearn s G εinv).Yes) ∧
          (∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n → x ∈ SATRel.No →
            f x ∈ (ExtensionLearn s G εinv).No) ∧
          WitnessMap SATRel (ExtensionLearn s G εinv) f gw := by sorry

end ProofCryptoSynergy.Supplement
