-- Prove2me | Theorems.Thm_PPSLattice_corollary_4_30
-- name    : PPSLattice.corollary_4_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:40:04.658536+00:00
-- url     : https://prove2.me/theorems/a6b597fd-8426-4ea8-b0c3-eee5820f829b
-- title:
--   Corollary 4.30 — a fully compact PPS from LWE with sub-exponential modulus-to-noise ratio
-- statement:
--   Let $0<\varepsilon<\tfrac12$ and let $(n,q(n),\chi(n))$ be an LWE parameter family with sub-exponential modulus-to-noise ratio: $q(n)$ prime, $1\le\chi(n)\le\mathrm{poly}(n)$, $q(n)/\chi(n)\ge2^{n^\varepsilon}$, both computable in polynomial time. If LWE is hard for this family, then there is a PPS scheme for $\mathcal M_\lambda=\{0,1\}^\lambda$, serving every number of indices $N$, such that
--
--   1. all its algorithms run in polynomial time;
--   2. it is correct: $\Pr[\mathrm{Decode}(S,\mathrm{sk}_S,i,\mathrm{ct})=\mu]=1$ for $N\le2^\lambda$, $i\in S\subseteq[N]$, $\mu\in\{0,1\}^\lambda$;
--   3. it is fully compact: $|\mathrm{crs}|,|\mathrm{msk}|,|\mathrm{ct}|,|\mathrm{sk}_S|\le\mathrm{poly}(\lambda,\log N)$ for $N\le2^\lambda$;
--   4. it is mode indistinguishable and
--   5. payload hiding (Definition 4.1);
--   6. its public-key ciphertexts are uniformly random strings.
--
--   This is the paper's main primitive: compactness in $\log N$ is what the flexible broadcast encryption compiler of §5 and the secret sharing schemes of §6 need.
--
--   Differences from the source:
--   - generalization: for any N ∈ N, there exists a PPS scheme for N indices → one scheme for all N (N an input of GSetup, chosen by the adversary in the games); reason: Definition 4.1's syntax and games take N as input; one scheme for all N implies a scheme for each N
--   - generalization: Corollary 4.30's conclusion → adds PkUniform: pkEnc(i) is uniform on {0,1}^{L(λ,N)}; reason: Theorem 1.1, the informal version of the same result, states it ('Moreover, public-key ciphertexts are uniformly random strings'); Remark 4.7
--   - reading: hardness of LWE with sub-exponential modulus-to-noise ratio → for every ε ∈ (0, ½) and every family (q(n), χ(n)) with q prime, 1 ≤ χ ≤ (n+2)^c, q/χ ≥ 2^{n^ε}, both computable in polynomial time: LWEHard q χ; reason: §4.3, p.20 ('χ = n, q a prime of size 2^{poly(λ,log N)} … q/χ = 2^{Õ(n^ε)} for any ε < 1/2'); one family is assumed hard, the goal quantifies over all
--   - reading: Assumption 3.4 with parameters (n, q, χ), m ∈ N → an ensemble indexed by the dimension n, for every polynomial-time computable sample count m(n); reason: the assumption leaves its index implicit; the reductions use polynomially many samples
--   - generalization: LWE against non-uniform PPT distinguishers (≈c, §3, p.15) → LWE against uniform PPT distinguishers; reason: a weaker hypothesis; the reductions map uniform adversaries to uniform distinguishers
--   - reading: polynomial time algorithms → PPS.Efficient: each law equals the image of fair coins under one polynomial-time machine, on every input; Decode a polynomial-time map; reason: §3, p.15 and §4.1, p.17
--   - reading: |crs| = poly_crs(λ, log N), … → every output has length ≤ (λ + ⌈log₂ N⌉ + 2)^c for all λ, 1 ≤ N ≤ 2^λ; reason: '=' is the upper-bound convention; the paper's own sizes are not polynomials in the real log N
--   - reading: message space M = {M_λ} → M_λ = {0,1}^λ; reason: the scheme of the corollary is Construction 4.6, 'a PPS scheme for M_λ = {0,1}^λ'
--   - reading: D_{Z,σ} with width parameter σ (no formula) → weights exp(−x²/(2σ²)); reason: the convention of [Lyu12], the source of Lemma 3.2
--   - reading: stateful (admissible) PPT adversary → uniform reactive machine RestrictedDec.Adversary (polynomial-time step function, polynomially many coins, bounded state, moves and activations); inadmissible runs scored as a uniform guess; reason: Definitions 4.1, 4.2, 4.4 say PPT adversary; the ½-convention is equivalent to admissibility because an adversary can test its own admissibility
--   - encoding: crs, keys, ciphertexts, messages, set descriptions; [N]; Z_q → bit strings Str (pairs via tup, numbers in binary, least significant bit first); [N] = Finset.Icc 1 N; Z_q = ZMod q; reason: Lean convention; same instances
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Corollary 4.30, p.31; Theorem 1.1, p.4; Definition 4.1, pp.17–18

import Mathlib
import Definitions.Def_PPSLattice_LWERegime
import Definitions.Def_PPSLattice_LWEHard
import Definitions.Def_PPSLattice_PPS_Efficient
import Definitions.Def_PPSLattice_PPS_Correct
import Definitions.Def_PPSLattice_PPS_FullyCompact
import Definitions.Def_PPSLattice_PPS_ModeInd
import Definitions.Def_PPSLattice_PPS_PayloadHiding
import Definitions.Def_PPSLattice_PPS_PkUniform
set_option autoImplicit false

namespace PPSLattice

/-- **Corollary 4.30** (with Theorem 1.1). Assume LWE is hard with sub-exponential modulus-to-noise ratio:
for some `0 < ε < ½` the family `(n, q(n), χ(n))` satisfies `LWERegime ε q χ` (`q` prime, `1 ≤ χ ≤ poly(n)`,
`q/χ ≥ 2^{n^ε}`, both computable) and `LWEHard q χ`. Then there is one PPS scheme for `M_λ = {0,1}^λ`, serving
every number of indices `N`, whose algorithms run in polynomial time and which is correct, fully compact,
mode-indistinguishable and payload-hiding (Definition 4.1), and whose public-key ciphertexts are uniformly
random strings.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Corollary 4.30, p.31 ("Assuming the hardness of LWE with sub-exponential modulus-to-noise ratio, for any
N ∈ N, there exists a programmable pseudorandom set sampler scheme for N indices"); Theorem 1.1, p.4
("Moreover, public-key ciphertexts are uniformly random strings"); Definition 4.1, pp.17–18.

**Formalization Note.** `N` is an input of GSetup and a choice of the adversary in both games, so one scheme
for all `N` is the paper's own notion and implies "for any N there exists a scheme". The LWE hypothesis
concerns one parameter family, quantified universally, so the scheme must work with whichever family is
hard. -/
theorem corollary_4_30 (ε : ℝ) (q χ : ℕ → ℕ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hreg : LWERegime ε q χ) (hLWE : LWEHard q χ) :
    ∃ E : PPS, E.Efficient ∧ E.Correct ∧ E.FullyCompact ∧ E.ModeInd ∧ E.PayloadHiding ∧
      E.PkUniform := by sorry

end PPSLattice
