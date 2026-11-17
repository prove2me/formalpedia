-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_56
-- name    : ProofCryptoSynergy.Supplement.theorem_56
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:53:30.519552+00:00
-- url     : https://prove2.me/theorems/cd130c97-8695-44ce-b46b-b5ac16cabd90
-- title:
--   Theorem 56 — NP-hardness of Total-Learn under nonuniform reductions
-- statement:
--   Assume that subexponentially secure iO and a subexponentially secure NIWI exist, and that $\mathsf{coNP}\not\subseteq\bigcap_{c\ge1}\text{io-}\mathsf{NTIME}[2^{n^{1/c}}]$. Then there is a polynomial $s'$ such that for all subexponential functions $g'$ and $(\varepsilon')^{-1}$, there is a P/poly half-Levin reduction from SAT to
--   $$\mathrm{Total\text{-}Learn}_{g',\varepsilon'}[s'].$$
--
--   It trades the uniform proof-complexity assumption of Theorem 46 for a weaker one at the price of nonuniformity.
--
--   Differences from the source:
--   - encoding: polynomial p(n) = n^c, c ≥ 1, with parameters s, g, ε⁻¹ : ℕ → ℕ → IsPolyFn: n ↦ ⌊n^c⌋, real c ≥ 1; reason: Definitions 21–27 take the parameters ℕ-valued; circuit sizes are naturals, so the floor changes no bound
--   - encoding: Pr < 1/2 + ε(n) → (Pr − 1/2)·ε⁻¹(n) < 1, the parameter being ε⁻¹ : ℕ → ℕ; reason: Definition 21 takes ε⁻¹ as the parameter; no division, and ε⁻¹(n) = 0 (ε undefined) is not the hardest case
--   - encoding: promise problems over strings (Definition 3); SAT with witness relation φ(w) = 1 → witness relations on sampling circuits and circuits, R_N containing the invalid instances; SAT witnesses with |w| ≤ |φ|; reason: N is exactly the set of no-instances; every variable index of φ is below |φ|, so SAT’s Y and N are unchanged
--   - encoding: P/poly reduction (circuits of polynomial size) → f, g computed by multi-output circuits of size ≤ (n+2)^c, one per length n = |φ|, reading padIn and writing unpadOut; reason: Definition 4’s nonuniform reductions with a polynomial bound
--   - encoding: subexponential g′, (ε′)⁻¹ → g′, ε′⁻¹ : ℕ → ℕ with the published IsSubexp (eventual bound 2^{n^{1/c}} for each c); reason: the base mission’s reading of §2.1; no positivity is added, the problems are monotone
--   - encoding: a poly(n)-size circuit E sampling (x, b) → every output of the reduction has description length at most (n+2)^c, n its input length, for one constant c (PolySizeOut / RandPolySizeOut); reason: “poly(n)-size” names no polynomial, so one polynomial per reduction; n + 2 avoids the zero bound at n = 0
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 56, p.44 (PDF 46)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_IsSubexp
import Definitions.Def_ProofCryptoSynergy_SubexpIOExists
import Definitions.Def_ProofCryptoSynergy_NIWIScheme
import Definitions.Def_ProofCryptoSynergy_Supplement_CoNPNotIoSubexpNTIME
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
import Definitions.Def_ProofCryptoSynergy_Supplement_CGL
import Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 56 (NP-hardness of Total-Learn under nonuniform reductions)** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.44 (PDF 46)). Assume subexponentially secure iO and a subexponentially secure
NIWI exist and `coNP ⊄ ⋂_{c≥1} io-NTIME[2^{n^{1/c}}]`. Then there exists a polynomial `s'` such that there is
a P/poly half-Levin reduction from SAT to `Total-Learn_{g',ε'}[s']`, where `g'` and `(ε')⁻¹` are arbitrary
subexponential functions.

**Formalization Note** `s'` is chosen before `g'` and `(ε')⁻¹`; the reduction may depend on them. P/poly:
`f` and `g` are computed by circuits of size at most `(n+2)^c`, one per input length `n = |φ|`.
The output samplers are instances of polynomial size in their input length (`PolySizeOut`; the
definitions of the learning problems: "a poly(n)-size circuit `E`"). -/
theorem theorem_56 :
    SubexpIOExists → SubexpNIWIExists → CoNPNotIoSubexpNTIME →
      ∃ s : ℕ → ℕ, IsPolyFn s ∧ ∀ g εinv : ℕ → ℕ,
        IsSubexp (fun n => (g n : ℝ)) → IsSubexp (fun n => (εinv n : ℝ)) →
        ∃ (c : ℕ) (f : List Bool → Samp) (gw : List Bool → List Bool → Wit),
          NonuHalfLevin (TotalLearn s g εinv) (fun n => (n + 2) ^ c) f gw ∧ PolySizeOut f := by sorry

end ProofCryptoSynergy.Supplement
