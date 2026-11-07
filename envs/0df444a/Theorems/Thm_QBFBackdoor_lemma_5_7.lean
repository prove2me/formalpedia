-- Prove2me | Theorems.Thm_QBFBackdoor_lemma_5_7
-- name    : QBFBackdoor.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:37.384345+00:00
-- url     : https://prove2.me/theorems/7e86cab0-91d6-4fab-98ee-965297f3686e
-- title:
--   Lemma 5.7 — squishing $\binom{k}{2^p}$ disjuncts into $k$
-- statement:
--   Let $k,p\ge1$ and $K=\binom{k}{2^p}$. There is a polynomial-time algorithm that maps every instance $\Phi=Q.(\phi_1\vee\cdots\vee\phi_K)$ of $K$-Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ with $m$ atoms to an instance $\Phi'$ of $k$-Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ such that:
--
--   1. $\Phi'$ is true if and only if $\Phi$ is true;
--   2. $\Phi'$ has at most
--   $$
--   m\cdot 2^p + k\cdot p
--   $$
--   atoms;
--   3. the prefix of $\Phi'$ is $Q$ followed by one existential block and one universal block.
--
--   Applied with $k=4$, $p=1$, it replaces six disjuncts by four. Repeating this in rounds reduces any number of disjuncts to four, at the cost of larger disjuncts and more quantifier blocks.
--
--   Differences from the source:
--   - generalization: O(kp + m2^p) atoms → at most m·2^p + k·p atoms; reason: the explicit count of the proof ("there are mr+kp output atoms", p.25), which implies the O-bound
--   - generalization: the conclusion of the lemma → also: the new prefix is Q followed by an existential and a universal block; reason: the proof states "appends at most two quantifier blocks" (p.25); dropping this clause gives the lemma
--   - encoding: a polynomial-time algorithm on K-Disjunct instances → a total map with Nonempty (Turing.TM2ComputableInPolyTime encDQBF encDQBF f), constrained only on instances with exactly K disjuncts; reason: Mathlib's TM2 polynomial time; values on other inputs are irrelevant
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), Lemma 5.7, p.24; proof, p.25

import Mathlib
import Definitions.Def_QBFBackdoor_encCNF

namespace QBFBackdoor

/-- **Lemma 5.7 (the squishing lemma).** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), p.24: "Let k and p be positive integers and
K = (k choose 2^p). There is a polynomial-time algorithm that takes an instance Φ of
K-Disjunct-QBF(ΓAFF) with m atoms and produces an equivalent instance Φ′ of k-Disjunct-QBF(ΓAFF)
with O(kp + m2^p) atoms." The proof (p.25): "there are mr+kp output atoms … The construction …
appends at most two quantifier blocks", namely `Q∃Y∃Z∀W`.

For all `k, p ≥ 1` there is a map `f` on Disjunct-QBF(ΓAFF) instances, computable in polynomial
time on the encodings, such that for every instance `Φ` with exactly `(k choose 2^p)` disjuncts and
`m` atoms: `f Φ` has exactly `k` disjuncts, `f Φ` is true iff `Φ` is, `f Φ` has at most
`m·2^p + k·p` atoms, and the prefix of `f Φ` is the prefix of `Φ` followed by an existential block
of `a` variables and a universal block of `w` variables.

**Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` for the
structural encoding `encDQBF`. `f` is total; only its values on `K`-disjunct instances are
constrained. The bound `O(kp + m2^p)` is stated as the explicit count of the proof. The quantifier
order (`k, p` first, then the algorithm) is the printed one. `K = 0` (when `2^p > k`) is allowed. -/
theorem lemma_5_7 (k p : ℕ) (hk : 1 ≤ k) (hp : 1 ≤ p) :
    ∃ f : DQBFInst → DQBFInst,
      Nonempty (Turing.TM2ComputableInPolyTime encDQBF encDQBF f) ∧
      ∀ I : DQBFInst, I.Φ.disj.length = Nat.choose k (2 ^ p) →
        (f I).Φ.disj.length = k ∧
        ((f I).Φ.holds ↔ I.Φ.holds) ∧
        (f I).Φ.atomCount ≤ I.Φ.atomCount * 2 ^ p + k * p ∧
        ∃ a w : ℕ, (f I).n = I.n + a + w ∧
          ∀ j : Fin (f I).n, (f I).Φ.q j =
            if hj : j.val < I.n then I.Φ.q ⟨j.val, hj⟩ else decide (j.val < I.n + a) := by sorry

end QBFBackdoor
