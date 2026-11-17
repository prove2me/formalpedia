-- Prove2me | Theorems.Thm_QuantumPRC_Supplement_theorem_9_8
-- name    : QuantumPRC.Supplement.theorem_9_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:40:48.418547+00:00
-- url     : https://prove2.me/theorems/98339151-289e-469a-9a5a-381b6b3083cd
-- title:
--   Theorem 9.8 — under LPN or LWE, robust keyed-QECCs whose codewords are hard to recognize
-- statement:
--   Suppose Assumption 5 holds. Then there are polynomial lengths $n_L<n_P$ with $n_L=\omega(\log\lambda)$ (so also $n_P=\omega(\log\lambda)$) and one keyed-QECC $(\mathrm{KeyGen},\mathrm{Enc},\mathrm{Dec})$ from $n_L$ to $n_P$ qubits (Definition 9.1: the syntax of Definition 4.3, with PPT key generation and QPT encoding and decoding) such that, for every function $w$ with
--
--   $$
--   w(n_P)=o\Big(n_P\,\frac{\log\log n_P}{\log n_P}\Big),
--   $$
--
--   the scheme, run with the parameter $W=\min(w(n_P),n_P)$,
--
--   1. is robust to every $w(n_P)$-local noise family $\mathcal E$ (Definition 3.7): $\big\|\mathbb E_{\mathsf{sk}}\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\mathsf{sk}}-\mathrm{id}\big\|_\diamond\le\mathrm{negl}(\lambda)$, and
--   2. satisfies the hardness of recognizing codewords (Definition 9.7): for every polynomial $t\ge1$, no uniform QPT learner with oracle access to $\mathrm{Enc}_{\mathsf{sk}}$ distinguishes $t$ copies of an encoded basis state from $t$ copies of a Haar-random state with non-negligible advantage.
--
--   By contrast, codewords of keyed stabilizer codes are easy to recognize (Proposition 9.4), and unbounded learners recognize codewords of any keyed-QECC (Proposition 9.6).
--
--   Differences from the source:
--   - generalization: for any w(nP) = o(nP log log nP / log nP), there exist keyed-QECCs (∀ w ∃ scheme) → ∃ nL nP S, ∀ w: one scheme, run at parameter W = min(w(nP), nP), serves every w; reason: stronger than the printed order and specializes to it; it is what the proof gives through Corollary 7.5, read the same way in the base mission (SUPPLEMENT.md decision 5)
--   - reading: keyed-QECC encoding nL into nP qubits (nL, nP unspecified; §4: polynomials with nL ≤ nP) → EffPoly nL, nP with nL < nP and log λ = o(nL), a ChScheme with Implementable and ChScheme.Robust for every IsLocalNoise (w ∘ nP) nP family; reason: Definition 9.1 with the base mission's model of Definition 4.3; the parameters are those the proof of Theorem 9.8 (p.67) obtains from Corollary 7.5 (nL < nP, nL, nP ≥ ω(log λ)), since with nL, nP unconstrained the statement is met trivially by nL ≡ nP ≡ 0 (codeword and Haar state are both the scalar 1)
--   - reading: no QPT learner can win CodeRec^(t)_D with probability at least 1/2 + 1/poly(λ), for any polynomial t → for every EffPoly t ≥ 1 and every uniform learner, ∃ negligible ν with Pr[win] ≤ 1/2 + ν(λ) for all λ; reason: the standard meaning of non-negligible advantage; a learner below 1/2 can flip its output
--   - encoding: Haar-random nP-qubit pure state |ψ⟩; challenge W(|x⟩⟨x|)^⊗t or |ψ⟩⟨ψ|^⊗t; oracle access after the challenge → |ψ⟩ = U|0^nP⟩ with U ~ unitaryHaar(2^nP); the challenge on the learner's first t·nP wires, |0⟩ elsewhere; queries in the base OCirc model; learners with fewer wires output 0; reason: a fixed representation of the game of Definition 9.2
--   - encoding: log → Real.log; o(·) as n → ∞ via radiusScale n = n log log n / log n; reason: o(·) is insensitive to the base of the logarithm and to finitely many values
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 9.8, p.67; Definitions 9.1, 9.2, p.65; Definition 9.7, p.67; Definition 4.3, p.25

import Mathlib
import Definitions.Def_QuantumPRC_Supplement_CodeRec
import Definitions.Def_QuantumPRC_GraphRecoverSpec

open Filter Asymptotics

namespace QuantumPRC.Supplement

/-- **Theorem 9.8** (keyed-QECCs whose codewords are hard to recognize). Hsieh, Yamada, *Quantum
Pseudorandom Error-Correcting Codes*, arXiv:2609.38986 (version of October 29, 2026, sha256
6901b59d…), Theorem 9.8, p.67: "Suppose that Assumption 5 is true. Then, for any
`w(nP) = o(nP log log nP / log nP)`, there exist keyed-QECCs that are robust to any `w(nP)`-local noise
and satisfy the hardness of recognizing codewords." A keyed-QECC (Definition 9.1, p.65) is a tuple of
QPT algorithms with the syntax and robustness of Definition 4.3; hardness is Definition 9.7 (p.67)
for the game of Definition 9.2 (p.65).

**Formalization Note.**
* One scheme serves every `w`, as in the base mission's Corollary 7.5: `nL, nP` and the scheme `S` are
  chosen before `w`, and `S` is run at the parameter `W = min(w(nP), nP)` (`capW`). This is stronger
  than the printed order (`∀ w, ∃` scheme).
* `w` is a function of `nP`, as printed; `o(·)` is as `n → ∞`, and `radiusScale n = n log log n / log n`
  (`Real.log`).
* The keyed-QECC is a `ChScheme` with `Implementable` (Definition 4.3 syntax) and robustness (43) for
  every `w(nP)`-local noise family (`∃ negl` after the family); `nL, nP` are `EffPoly`.
* The printed theorem does not name `nL, nP`. Taken literally it would be met by `nL ≡ nP ≡ 0`, where
  codeword and Haar state are both the scalar `1` and every learner wins with probability exactly
  `1/2`. The statement therefore asks for the parameters the proof of Theorem 9.8 (p.67) obtains from
  Corollary 7.5: `nL(λ) < nP(λ)` and `nL(λ), nP(λ) ≥ ω(log λ)` (here `log λ = o(nL)`, and `nP > nL`). -/
theorem theorem_9_8 (hA : Assumption5) :
    ∃ nL nP : ℕ → ℕ, EffPoly nL ∧ EffPoly nP ∧ (∀ lam, nL lam < nP lam) ∧
      (fun lam : ℕ => Real.log lam) =o[atTop] (fun lam => (nL lam : ℝ)) ∧
      ∃ S : ChScheme nL nP, S.Implementable ∧
        ∀ w : ℕ → ℕ, (fun n => (w n : ℝ)) =o[atTop] (fun n => radiusScale n) →
          (∀ E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam)),
              IsLocalNoise (fun lam => w (nP lam)) nP E →
                S.Robust (ChScheme.capW (fun lam => w (nP lam)) nP) E) ∧
            HardToRecognize S (ChScheme.capW (fun lam => w (nP lam)) nP) := by sorry

end QuantumPRC.Supplement
