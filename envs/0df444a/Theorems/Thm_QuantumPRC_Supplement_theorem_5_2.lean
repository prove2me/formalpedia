-- Prove2me | Theorems.Thm_QuantumPRC_Supplement_theorem_5_2
-- name    : QuantumPRC.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:38:52.812764+00:00
-- url     : https://prove2.me/theorems/43a8582f-507b-46f8-b2f3-b6d1b81e12b2
-- title:
--   Theorem 5.2 — Construction 5.1 is a public-key QPRC robust to every $t$-local noise
-- statement:
--   Let $p\in(0,\tfrac12)$ and let $n_L,t,m,\ell$ be polynomial lengths. Let $(\mathrm{QECC.Enc},\mathrm{QECC.Dec})$ be a QECC for $t$-local noise encoding $n_L$ qubits into $\ell$ qubits (Definition 3.9), and let $(\mathrm{PRC.KeyGen},\mathrm{PRC.Enc},\mathrm{PRC.Dec})$ be a $(2\ell,m)$ public-key PRC that is robust to every $p$-bounded noise channel (Definitions 3.6, 3.19). If
--
--   $$
--   t(\lambda)\le p\cdot m(\lambda)\qquad\text{for all sufficiently large }\lambda,
--   $$
--
--   then the scheme of Construction 5.1, encoding $n_L$ qubits into $n_P=\ell+m$ qubits, is a public-key QPRC robust to every $t$-local noise, for the ideal distribution that outputs the completely depolarizing channel $\rho\mapsto\operatorname{Tr}(\rho)I/2^{n_P}$ with probability one:
--
--   1. its KeyGen is PPT and its encoder and decoder are QPT;
--   2. for every $t$-local noise family $\mathcal E$ on $n_P$ qubits, $\big\|\mathbb E_{(\mathsf{pk},\mathsf{sk})}\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\mathsf{pk}}-\mathrm{id}\big\|_\diamond\le\mathrm{negl}(\lambda)$;
--   3. no QPT adversary given $\mathsf{pk}$ and quantum oracle access distinguishes $\mathrm{Enc}_{\mathsf{pk}}$ from the completely depolarizing channel with non-negligible advantage.
--
--   Combined with existing QECCs and the PRCs of Theorem 3.26, this yields public-key and secret-key QPRCs with constant rate robust to linear-weight local noise (Corollary 5.3).
--
--   Differences from the source:
--   - generalization: nL, t, m, ℓ are polynomials → EffPoly lengths; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (base convention)
--   - reading: PRC.Enc is a PPT algorithm with internal randomness r → the base PKPRC with coin count ec, assumed EffPoly (polynomially bounded and computable from 1^λ in polynomial time); reason: a PPT algorithm runs in time bounded by a fixed polynomial, which bounds and fixes its coin count; the base PKPRC.Efficient records only PolyBounded ec, too weak for printing the encoding circuit
--   - reading: QPT algorithms and adversaries (no machine model given) → the base model: Clifford+T circuits (with oracle queries) printed by a polynomial-time Turing machine; KeyGen a polynomial-time function of fair coins; reason: the paper fixes no model; this is the base mission's model (paper.md decision 3), and the constructed KeyGen is PRC.KeyGen, which is PPT
--   - reading: a QECC for t-local noise that encodes nL qubits into ℓ qubits → QECC.IsQECCFor t: an isometric encoder, QPT encoder and decoder, and (23) for every t-local family on ℓ qubits with the negligible function chosen after the family; reason: Definition 3.9 fixes the family first (SUPPLEMENT.md decision 6)
--   - encoding: a (2ℓ, m) public-key PRC robust to any p-bounded noise → P : PKPRC (2ℓ) m with ∀ E, IsPBounded p E → P.IsPRC E; reason: the meaning of the phrase, as in the base Theorem 3.26
--   - encoding: is a public-key QPRC robust to any t-local noise (ideal: completely depolarizing channel) → IsQPRCLocal t: Implementable, Robust E for every IsLocalNoise t (ℓ+m) family, and Pseudorandom against depolarizing (nL) (ℓ+m) with pk as the adversary's input; reason: Definition 4.1 with the ideal distribution of §5
--   - encoding: registers B (ℓ qubits) and C (m qubits) of nP = ℓ + m; message x∥z → B is the first ℓ qubits, C the last m; x∥z is catB x z; reason: a fixed layout; changes no instance
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 5.2 and Construction 5.1, p.28; Definitions 3.6, 3.7, 3.9, 3.19, 4.1

import Mathlib
import Definitions.Def_QuantumPRC_Supplement_C51

open Filter

namespace QuantumPRC.Supplement

/-- **Theorem 5.2** (Construction 5.1 is a public-key QPRC). Hsieh, Yamada, *Quantum Pseudorandom
Error-Correcting Codes*, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d…), Theorem 5.2,
p.28: "Let `p ∈ (0, 1/2)`. If `t(λ) ≤ p · m(λ)` for sufficiently large `λ`, then Construction 5.1 is a
public-key QPRC robust to any `t`-local noise." Setting of Construction 5.1, p.28: "Let `p ∈ (0, 1/2)`.
Let `nL, t, m, ℓ : ℕ → ℕ` be polynomials. Let `(QECC.Enc, QECC.Dec)` be a QECC for `t`-local noise that
encodes `nL` qubits into `ℓ` qubits. Let `(PRC.KeyGen, PRC.Enc, PRC.Dec)` be a `(2ℓ, m)` public-key PRC
robust to any `p`-bounded noise. Define `nP := ℓ + m`." The ideal distribution is the point mass on the
completely depolarizing channel (§5, p.28).

**Formalization Note.**
* "Is a public-key QPRC robust to any `t`-local noise" is `IsQPRCLocal t`: efficient KeyGen, Enc and
  Dec (exact circuits), robustness (41) for every `t`-local family on `ℓ + m` qubits (`∃ negl` after
  the family) and pseudorandomness (42) against the completely depolarizing channel, with `pk` given
  to the adversary.
* "A QECC for `t`-local noise" is `QECC.IsQECCFor t`; "a PRC robust to any `p`-bounded noise" is
  `∀ E, IsPBounded p E → P.IsPRC E` (Definitions 3.6, 3.19), as in the base mission's Theorem 3.26.
* "Polynomials" are `EffPoly` lengths. The number `ec(λ)` of coins of PRC.Enc is also `EffPoly`: in
  the paper PRC.Enc is a PPT algorithm, whose coin count is a polynomial in `λ`.
* Register order: `B` (QECC block, Pauli pad) is the first `ℓ` qubits, `C` (PRC ciphertext) the last
  `m`. -/
theorem theorem_5_2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) (nL t m ℓ : ℕ → ℕ)
    (hnL : EffPoly nL) (ht : EffPoly t) (hm : EffPoly m) (hℓ : EffPoly ℓ)
    (Q : QECC nL ℓ) (hQ : Q.IsQECCFor t)
    (P : PKPRC (fun lam => 2 * ℓ lam) m) (hP : ∀ E : CNoise m, IsPBounded p E → P.IsPRC E)
    (hec : EffPoly P.ec)
    (htm : ∀ᶠ lam in atTop, (t lam : ℝ) ≤ p * m lam) :
    (C51.scheme Q P).IsQPRCLocal t := by sorry

end QuantumPRC.Supplement
