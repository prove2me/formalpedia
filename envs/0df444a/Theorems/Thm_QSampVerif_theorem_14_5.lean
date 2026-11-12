-- Prove2me | Theorems.Thm_QSampVerif_theorem_14_5
-- name    : QSampVerif.theorem_14_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:40:08.046198+00:00
-- url     : https://prove2.me/theorems/600b8d10-02f3-4bae-b2f0-9d08da821601
-- title:
--   Theorem 14.5 (pinned-down) — under subexponential QFHE, a classical PPT verifier samples any quantum circuit with error $e^{-c\lambda}$ against efficient provers
-- statement:
--   This is the operator-requested **pinned-down version** of Theorem 14.5, the formal version of the headline Theorem 1.2: the paper's informal computational model, adversaries and QFHE are given precise definitions, each declared below.
--
--   Suppose some QFHE scheme is subexponentially secure (Definition 3.20 with the bounds of Assumption 3.21). Then there exist a classical PPT verifier $V$, a uniform QPT honest prover $P^*$ and a constant $c>0$ such that:
--
--   1. **Correctness.** There is $\lambda_0$ such that for every $\lambda\ge\lambda_0$ and every well-formed target circuit $C$,
--   $$\Pr[V\leftrightarrow P^*(\lambda,C)\ \text{outputs}\ \bot]\le e^{-c\lambda}\qquad\text{and}\qquad \mathrm{TV}\bigl(D_{\mathrm{real}},P_C\bigr)\le e^{-c\lambda},$$
--   where $D_{\mathrm{real}}$ is the verifier's output distribution and $P_C$ gives $\bot$ probability zero.
--   2. **Soundness.** For every polynomial $q$ there is $\lambda_0$ such that for every $\lambda\ge\lambda_0$, every well-formed target circuit $C$, every prover $P$ and every quantum distinguisher $D$ with $\mathrm{size}(P),\mathrm{size}(D)\le q(\lambda+|C|)$,
--   $$\Bigl|\Pr_{z\sim D_{\mathrm{real}}}[D(z)=1]-\Pr_{z\sim D_{\mathrm{ideal}}}[D(z)=1]\Bigr|\le e^{-c\lambda},$$
--   where $D_{\mathrm{ideal}}$ returns a fresh sample of $P_C$ with probability $p$ and $\bot$ with probability $1-p$, and $p$ is the actual acceptance probability of $V$ with this $P$.
--
--   The theorem gives classical verification of quantum sampling with exponentially small error in the security parameter, whereas earlier protocols had inverse-polynomial soundness error.
--
--   Differences from the source:
--   - reading: Protocol 14.1, "with the parameter choices above", satisfies the two clauses → some classical PPT verifier V and some uniform QPT honest prover P* satisfy them (∃ V P* c); reason: Protocol 14.1 cannot be written out from the paper (its RSP layer is the [HN26] interface of Definition 12.1, p.128, and its compiler is the [BFK09] brickwork compiler by reference, p.182); Theorem 1.2 (p.2) states the existential headline, and Protocol 14.1 is its witness
--   - reading: "let C be a quantum circuit with output distribution P_C" → a well-formed layered circuit over the published Clifford+T instructions (H, S, T, X, CNOT) on |0…0⟩ with distinct measured output wires; reason: the paper fixes no gate set; §14.1 uses fixed Clifford+T decompositions and compiles into H and CCZ, which Clifford+T expresses exactly
--   - encoding: classical PPT verifier, QPT prover, nonuniform provers with classical advice, the interaction → ClassicalVerifier (PolyTimeComputable next/output on a view with messages cut to a polynomial bound; polynomially bounded, computable rounds, coins and bound; speaks first), Prover (persistent core from |0…0⟩, padEnc message loading by X flips, Clifford+T rounds, computational-basis replies), QPT = well formed with a PolyTimeComputable description, and the Born-rule semantics averaged over the verifier's coins; reason: the model of §3.11, p.23 ("polynomial-size quantum circuits with nonuniform classical advice"), written out (paper.md decisions 4–7)
--   - encoding: inputs λ_sec and C; |C| → common input ⟨1^λ, ⟨C⟩⟩ as a uniquely decodable tuple; |C| the length of the description of C; reason: paper.md decision 4; the published encStr is not uniquely decodable
--   - reading: "any efficient malicious quantum prover", "computationally indistinguishable" → every prover and every quantum distinguisher (nonuniform, classical advice) of size ≤ q(λ + |C|), for every polynomial q; provers need not be well formed; reason: the standard meaning; "allowed circuits" (p.24) is a device inside the proof (paper.md decisions 8, 11)
--   - generalization: "negligible" rejection probability, TV distance and distinguishing advantage → e^{−cλ} with one c > 0 for both clauses, uniform in C beyond λ₀, and c fixed before the polynomial q; reason: §14.3 (pp.186–188) and Lemma 14.4 derive e^{−Ω(λ_sec)}; e^{−cλ} is negligible, so the statement specializes to the printed one
--   - generalization: Definition 3.20 item 1: correctness for every evaluated circuit → correctness only for well-formed classical-output circuits of depth ≤ L and size ≤ e^{c₁κ^a}, with the trace distance averaged over the coins of Gen and Enc; reason: a weaker hypothesis gives a stronger theorem; the protocol only evaluates polynomial-size classical-output circuits ("For circuits with classical outputs, the evaluated ciphertext and its decryption are also classical", p.24)
--   - reading: Assumption 3.21: the bounds hold for every κ → the bounds hold for every κ ≥ κ₀ (and every depth bound L); reason: a weaker hypothesis, equivalent to the printed one under κ ↦ κ + κ₀ (paper.md decision 13)
--   - encoding: the QFHE algorithms, IND-CPA security, correctness error → Gen, Enc, Dec PolyTimeComputable with polynomial computable coin counts; Eval a circuit produced by a PolyTimeComputable map from (ek, ⟨C⟩, ct); the IND-CPA game with a classical challenger (ek first, encryption oracle throughout, one challenge given as the two halves of one string, ⊥ on odd length) against well-formed adversaries (Prover.Valid) of size ≤ e^{c₁κ^a}; the trace distance in variational (Helstrom) form; reason: Definition 3.20 written out in the mission's circuit model (paper.md decision 12); a malformed adversary (repeated wires) is simulated by a well-formed one with constant-factor overhead, absorbed in c₁
--   - reading: Definition 3.20 item 3: "Decryption takes time polynomial in κ and the output length, independently of the evaluated circuit" → the evaluated ciphertext has length |ct′| ≤ p(κ + output length of C) for every κ, L, key coins, circuit, plaintext and encryption coins, and Dec is PolyTimeComputable on ⟨sk, ct′⟩; reason: the circuit-independent time bound is read as a bound on the length of what Dec reads (the output ciphertext), with Dec polynomial time in its input; this is the property the classical verifier uses to decrypt the prover's answers in polynomial time
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Theorem 14.5, p.189 (PDF 190); Theorem 1.2, p.2 (PDF 3); Definition 3.20 and Assumption 3.21, pp.23–24 (PDF 24–25); §14.3 and Lemma 14.4, pp.186–188

import Definitions.Def_QSampVerif_ClassicalVerifier
import Definitions.Def_QSampVerif_QDistinguisher
import Definitions.Def_QSampVerif_IsSubexpQFHE

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- Chung, Cojocaru, Lee, Lin, *Classical Verification of Quantum Sampling with Negligible
Error*, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Theorem 14.5 (Classical
verification with negligible error), p.189 (PDF 190), as the formal version of Theorem 1.2
(p.2, PDF 3); operator-requested pinned-down version.

If some QFHE scheme satisfies Definition 3.20 with the bounds of Assumption 3.21, then there are
a classical PPT verifier `V`, a uniform QPT honest prover `P*` and a constant `c > 0` such that
* (correctness) for all `λ` beyond some `λ₀` and every target circuit `C`, the honest prover is
  rejected with probability at most `e^{−cλ}` and the verifier's output distribution is within
  total variation distance `e^{−cλ}` of `P_C`;
* (soundness) for every polynomial `q` there is `λ₀` such that for all `λ ≥ λ₀`, every target
  circuit `C`, every prover `P` and every quantum distinguisher `D`, both of size at most
  `q(λ + |C|)`, `D` distinguishes the verifier's output from `D_ideal` (a fresh sample of `P_C`
  with the actual acceptance probability `p`, else `⊥`) with advantage at most `e^{−cλ}`.

**Formalization Note.** The protocol is existentially quantified (Protocol 14.1 is its witness);
target circuits are Clifford+T layered circuits on `|0…0⟩`; "negligible" is `e^{−cλ}`, one `c`
for both clauses, fixed before the adversary's polynomial (paper.md decisions 2–13). -/
theorem theorem_14_5 :
    (∃ S : QFHEScheme, IsSubexpQFHE S) →
    ∃ (V : ClassicalVerifier) (Pstar : ℕ → TargetCircuit → Prover) (c : ℝ),
      V.IsPPT ∧ IsQPTProver Pstar ∧ 0 < c ∧
      (∃ lam₀ : ℕ, ∀ lam : ℕ, lam₀ ≤ lam → ∀ C : TargetCircuit, C.Valid →
        outDist V (Pstar lam C) lam C none ≤ Real.exp (-(c * lam)) ∧
        tvDist (outDist V (Pstar lam C) lam C) C.pushSome ≤ Real.exp (-(c * lam))) ∧
      (∀ q : Polynomial ℕ, ∃ lam₀ : ℕ, ∀ lam : ℕ, lam₀ ≤ lam → ∀ C : TargetCircuit, C.Valid →
        ∀ P : Prover, P.size ≤ q.eval (lam + C.encode.length) →
        ∀ D : QDistinguisher, D.size ≤ q.eval (lam + C.encode.length) →
          advantage D (outDist V P lam C) (idealDist V P lam C) ≤ Real.exp (-(c * lam))) := by sorry

end QSampVerif
