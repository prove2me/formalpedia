-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_72
-- name    : ProofCryptoSynergy.Supplement.theorem_72
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:57:25.310199+00:00
-- url     : https://prove2.me/theorems/bd2f3162-278a-4f79-b68b-0d16758087ee
-- title:
--   Theorem 72 — Levin NP-hardness of CGL ⟺ extractable witness encryption
-- statement:
--   The following are equivalent:
--
--   1. **(Levin NP-hardness of CGL)** there exist a polynomial $s$ and a tuple of machines $(f,g,h)$, with $f,g$ deterministic and $h$ possibly randomized, such that for all polynomial $G$ and $\varepsilon^{-1}$, $(f,g,h)$ is an honest Levin reduction from SAT to $\mathrm{CGL}_{G,\varepsilon}[s]$;
--   2. extractable witness encryption exists.
--
--   It identifies extractability of witness encryption with witness recovery in the learning reduction.
--
--   Differences from the source:
--   - reading: witness encryption (Section 6, unqualified) → polynomially secure WE for SAT (IsPolyWE); reason: Section 6 is the polynomial regime; every WE there is for SAT
--   - reading: a pair (tuple) of machines; no time bound printed → polynomial-time machines (UnifPoly), timed on all inputs and fixed before G, ε⁻¹; reason: Lemma 75 runs f inside a polynomial-time Enc and Lemma 76 builds polynomial-time f, g; one machine must serve every G
--   - reading: Levin reduction in which h may be randomized → h a randomized polynomial-time machine; for every φ and every w′ with (f(φ), w′) ∈ R_N, Pr[h(φ, w′) satisfies φ] ≥ 1 − 1/100; reason: Definition 4’s witness recovery with Definition 5 1(b) for the randomized h, at the default ε = 1/100 of p.17
--   - encoding: honest: |f(x)| ≥ |x|^δ → length of the description MCircuit.code of the output sampler ≥ |x|^δ; reason: |f(x)| is the length of f’s output
--   - encoding: polynomial p(n) = n^c, c ≥ 1, with parameters s, g, ε⁻¹ : ℕ → ℕ → IsPolyFn: n ↦ ⌊n^c⌋, real c ≥ 1; reason: Definitions 21–27 take the parameters ℕ-valued; circuit sizes are naturals, so the floor changes no bound
--   - encoding: Pr < 1/2 + ε(n) → (Pr − 1/2)·ε⁻¹(n) < 1, the parameter being ε⁻¹ : ℕ → ℕ; reason: Definition 21 takes ε⁻¹ as the parameter; no division, and ε⁻¹(n) = 0 (ε undefined) is not the hardest case
--   - encoding: promise problems over strings (Definition 3); SAT with witness relation φ(w) = 1 → witness relations on sampling circuits and circuits, R_N containing the invalid instances; SAT witnesses with |w| ≤ |φ|; reason: N is exactly the set of no-instances; every variable index of φ is below |φ|, so SAT’s Y and N are unchanged
--   - encoding: a poly(n)-size circuit E sampling (x, b) → every output of the reduction has description length at most (n+2)^c, n its input length, for one constant c (PolySizeOut / RandPolySizeOut); reason: “poly(n)-size” names no polynomial, so one polynomial per reduction; n + 2 avoids the zero bound at n = 0
--   - reading: for all polynomial G, ε⁻¹, (f, g, h) is a Levin reduction to CGL (on every input) → every f(φ) is a CGL instance; yes-instances and witnesses are mapped for every φ; for each G, ε⁻¹, the no-part and witness recovery hold for all sufficiently long φ; reason: read for every φ, the no-condition forces perfectly balanced labels on every unsatisfiable φ (NP = coNP); Lemmas 75–76 give the asymptotic form
--   - reading: Definition 67: for any polynomial q, q(n)-size A and x ∈ {0,1}ⁿ (every n) → for each q = n^c, for all sufficiently large n; reason: Definition 67 extends Definition 13, whose properties hold for large n; read for every n it forces Enc(x,0) and Enc(x,1) to be identically distributed for unsatisfiable x with |x| ≥ 2 (NP = coNP), and Lemma 75 (Item 1) only yields extraction for large n
--   - encoding: Pr_{b,Enc}[A(x, Enc(x,b)) = b] ≥ 1/2 + 1/q(n); PPT extractor E(x, A) → (Pr − 1/2)·n^c ≥ 1 with A reading padIn k (x ++ ct); extractor polynomial-time in |x| + |code A| with polynomially many coins; reason: no division; adversaries read strings as in the published Indist
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 72, p.53 (PDF 55)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
import Definitions.Def_ProofCryptoSynergy_Supplement_CGL
import Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyWE

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 72** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.53 (PDF 55)). The following are equivalent.
* (Levin NP-hardness of CGL) There exist a polynomial `s` and a tuple of machines `(f, g, h)` such that, for
  all polynomial `G`, `ε⁻¹`, `(f, g, h)` is an honest Levin reduction from SAT to `CGL_{G,ε}[s]` in which `f`
  and `g` are deterministic and `h` may be randomized.
* Extractable witness encryption exists.

**Formalization Note** `f`, `g` are deterministic polynomial-time machines and `h` a randomized
polynomial-time machine (time polynomial in its input `(φ, w')`, polynomially many coins), all fixed before
`G`, `ε⁻¹`. Witness recovery is Definition 5, 1(b): for every `φ` and every `w'` with `(f(φ), w') ∈ R_N` of
CGL, `h(φ, w')` is a satisfying assignment of `φ` with probability at least `1 − 1/100` (the default of
p.17). Witness encryption is the polynomially secure `IsPolyWE` for SAT. Every `f(φ)` is a CGL instance of
polynomial size in its input length (`PolySizeOut`, Definition 21: "a poly(n)-size circuit"). For each
polynomial `G`, `ε⁻¹`, the no-part of the many-one condition and witness recovery (`RandRecover`) are
required for all sufficiently long `φ` (threshold depending on `G`, `ε⁻¹`), and extractability for all
large `n` (`ExtractableWE`); read for every input, both sides would force perfectly hiding encryptions of
unsatisfiable formulas (`NP = coNP`), while Lemmas 75–76 prove the asymptotic forms. -/
theorem theorem_72 :
    (∃ s : ℕ → ℕ, IsPolyFn s ∧ ∃ (f : List Bool → Samp) (gw : List Bool → List Bool → Wit)
        (h : List Bool → Wit → List Bool → List Bool) (hc : ℕ → ℕ → ℕ),
        UnifPoly f gw ∧ RandPolyMachine h hc ∧ Honest f ∧ PolySizeOut f ∧ (∀ x, (f x).WF) ∧
        ∀ G εinv : ℕ → ℕ, IsPolyFn G → IsPolyFn εinv →
          (∀ x ∈ SATRel.Yes, f x ∈ (CGL s G εinv).Yes) ∧
          (∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n → x ∈ SATRel.No →
            f x ∈ (CGL s G εinv).No) ∧
          WitnessMap SATRel (CGL s G εinv) f gw ∧
            RandRecover (CGL s G εinv) f h hc (1 / 100)) ↔
      ∃ E : WEForSAT, IsPolyWE E ∧ ExtractableWE E := by sorry

end ProofCryptoSynergy.Supplement
