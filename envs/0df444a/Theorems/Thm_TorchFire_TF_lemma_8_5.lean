-- Prove2me | Theorems.Thm_TorchFire_TF_lemma_8_5
-- name    : TorchFire.TF.lemma_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:48:47.858434+00:00
-- url     : https://prove2.me/theorems/ad4961d0-33f8-45cc-bbec-48adbca7b8b1
-- title:
--   Lemma 8.5 — witnesses for $m+1$ distinct labels from $m$ torches only with negligible probability
-- statement:
--   Let $A^W$ be a quantum procedure following the issuance rules of the global non-proliferation experiment (Definition 6.2), receiving only the $m$ issued torch registers, and making polynomially many public-oracle queries. For witnesses defined by (88) — a torch key $t\in T_{\mathrm{pub}}$, a request serial $s'=(\ell',a')$, and a valid torch signature $\sigma_T$ on $M_T(s',t)$ —
--   $$p_{\mathrm{wit}}:=\Pr[A^W\text{ outputs valid witnesses for }m+1\text{ distinct labels}]\le\mathrm{negl}(\lambda).$$
--   The procedure may process all pre-split and challenge flames jointly. (Polynomially bounded $R,m,N$ with $m\le R$, polynomially many sparks.)
--
--   Witnesses for $m+1$ distinct labels from $m$ torches would be two torch signatures on distinct messages under one key, or a signature under an unissued torch; Lemma 8.5 bounds the extraction term of (72) by torch OSS security.
--
--   Differences from the source:
--   - generalization: QPT adversaries → oracle algorithms with arbitrary finite workspace and unitaries; only the number of queries is bounded; reason: every QPT oracle algorithm is one with polynomially many queries (p.18); paper.md decision 2
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - encoding: polynomially many spark queries → a polynomially bounded spark count v(λ); reason: normal form of the games
--   - encoding: polynomially bounded R, m, N with 0 ≤ m ≤ R → functions ℕ → ℕ, each PolyBounded, with m(λ) ≤ R(λ) for every λ; reason: paper.md decision 15
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: probabilities over oracle sampling, algorithmic randomness and measurement outcomes → averages over the uniform finite oracle sample of Tr(Eρ) for the final cq-state, measurements deferred (Fact 3.1); reason: paper.md decision 6
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - reading: A^W following the issuance rules of Definition 6.2 → two stages: the v pre-split flames, a measured request J, then the torches of J and the N challenge flames, and m + 1 measured witnesses; reason: paper.md decision 4
--   - reading: valid witnesses for m + 1 distinct labels → m + 1 witnesses (s′, t, σ_T), each with t ∈ T_pub and a valid torch signature on M_T(s′, t), with pairwise distinct labels ℓ′; reason: (88)
--   - generalization: public-oracle queries in the modified experiment → queries to the full public collection (47); reason: a Γ⁰_i query is one controlled Γ query, so the class contains the modified procedures
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 8.5, p.74; (86), (88) p.70

import Mathlib
import Definitions.Def_TorchFire_TF_witnessProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.TF

/-- **Lemma 8.5**, p.74 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Let `A^W` be a quantum procedure following the issuance rules of the
global non-proliferation experiment (Definition 6.2), receiving only the `m` issued torch registers, and
making polynomially many public-oracle queries; it may process all pre-split and challenge flames
jointly. For witnesses defined by (88),
`p_wit := Pr[A^W outputs valid witnesses for m + 1 distinct labels] ≤ negl(λ)`
(for polynomially bounded `R, m, N, v` with `m ≤ R`). -/
theorem lemma_8_5 (R m N v Q : ℕ → ℕ) (hR : PolyBounded R) (hm : PolyBounded m)
    (hN : PolyBounded N) (hv : PolyBounded v) (hQ : PolyBounded Q) (hmR : ∀ lam, m lam ≤ R lam)
    (A : (lam : ℕ) → WitnessAdv lam (R lam) (m lam) (N lam) (v lam))
    (hA : ∀ lam, (A lam).QueryBounded (Q lam)) :
    Negligible fun lam => witProb (A lam) := by sorry

end TorchFire.TF
