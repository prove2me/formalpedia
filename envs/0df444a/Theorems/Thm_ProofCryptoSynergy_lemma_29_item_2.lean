-- Prove2me | Theorems.Thm_ProofCryptoSynergy_lemma_29_item_2
-- name    : ProofCryptoSynergy.lemma_29_item_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:47.655842+00:00
-- url     : https://prove2.me/theorems/886e41e5-3d5a-43e7-8cca-6a1b520ae6fd
-- title:
--   Lemma 29, item 2 — no optimal PPS iff every family $R_c$ true on SAT is fooled by a P-computable unsatisfiable family
-- statement:
--   There is no infinitely-often subexponentially optimal proof system iff the following holds. For every family $R_c(\psi)=\forall w\,P_c(\psi,w)$, $c\ge1$, with $|w|\le 2^{|\psi|^{1/c}}$, $P_c(\psi,w)$ computable in time $2^{O(|\psi|^{1/c})}$, and $R_c(\psi)$ true for all $\psi\in\mathrm{SAT}$, there are a constant $c^*\ge1$ and a P-computable family of unsatisfiable formulas $\psi_n$ of length $n$ such that for all large $n$,
--   $$R_{c^*}(\psi_n)\ \text{is true}.$$
--
--   So a property that all satisfiable formulas have, and that is checkable in subexponential co-nondeterministic time, is also held by some efficiently generated unsatisfiable formulas.
--
--   Differences from the source:
--   - reading: an arbitrary family of formulas R_c, indexed by c ≥ 1 → one machine computing P_c(ψ, w) from (1^c, ψ, w); time 2^{a_c |ψ|^{1/c}} with a_c depending on c; reason: the printed proof needs one polynomial-time PPS L_R checking transcripts of P_c for c given in the proof (p.26)
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: P_c(ψ, w) computable in time 2^{O(|ψ|^{1/c})} for all ψ → the time bound is required for nonempty ψ only; reason: at |ψ| = 0 the bound 2^{a_c·0} = 1 step cannot even read the input; only the empty formula is excluded, and R_c(ψ) for one fixed length plays no role in any clause (all are eventual or concern ψ ∈ SAT, which excludes the empty string)
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 29, item 2, pp.25–26 (PDF 27–28)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_PiFamily

namespace ProofCryptoSynergy

/-- **Lemma 29, item 2** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), pp.25–26 (PDF 27–28)). There is no infinitely-often subexponentially optimal proof system iff for
every family `R_c(ψ) = ∀w P_c(ψ, w)`, `|w| ≤ 2^{|ψ|^{1/c}}`, `P_c` computable in time `2^{O(|ψ|^{1/c})}`, with `R_c(ψ)` true for all
`ψ ∈ SAT`, there are a constant `c* ≥ 1` and a P-computable family of unsatisfiable `ψ_n` of length `n` with `R_{c*}(ψ_n)` true for all
large `n`.

**Formalization Note** The family is one machine on `(1^c, ψ, w)`, as the printed proof needs (`PiFamily`). -/
theorem lemma_29_item_2 :
    NoIoSubexpOptimalPPS ↔
      ∀ F : PiFamily, F.TimeBounded → (∀ c : ℕ, 1 ≤ c → ∀ ψ ∈ SAT, F.R c ψ) →
        ∃ (cs : ℕ) (ψ : ℕ → List Bool), 1 ≤ cs ∧ IsPUniformUnsat ψ ∧
          ∀ᶠ n : ℕ in Filter.atTop, F.R cs (ψ n) := by sorry

end ProofCryptoSynergy
