-- Prove2me | Theorems.Thm_QBennettGill_lemma_9
-- name    : QBennettGill.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:37.55971+00:00
-- url     : https://prove2.me/theorems/67974ad8-0d5a-4947-8d11-a58db8bd42bf
-- title:
--   Lemma 9 — outputs of a random oracle are pseudorandom against query-bounded adversaries
-- statement:
--   Let $q$ be a polynomial and let $\mathcal A=(\mathcal A_n)_n$ be adversaries, where $\mathcal A_n$ receives a string $y\in\{0,1\}^n$ and makes $q(n)$ quantum queries to $O_n:\{0,1\}^n\to\{0,1\}^n$. Its initial state and unitaries are arbitrary. Then there is a negligible $\mathrm{negl}$ with, for all $n$,
--
--   $$\Big|\Pr\big[\mathcal A^{|O_n\rangle}(1^n,O_n(x))=1:x\xleftarrow{\$}\{0,1\}^n,\,O_n\leftarrow\mathcal O_n\big]-\Pr\big[\mathcal A^{|O_n\rangle}(1^n,y)=1:y\xleftarrow{\$}\{0,1\}^n,\,O_n\leftarrow\mathcal O_n\big]\Big|\le\mathrm{negl}(n).$$
--
--   This is the pseudorandomness requirement of a PRHF (Definition 6, item 2) for a random oracle, from [HXY19, Theorem 2].
--
--   Differences from the source:
--   - generalization: for all QPT oracle-aided adversaries A → for every family of q(n)-query algorithms (q a polynomial) with arbitrary initial states and unitaries; reason: the [HXY19] bound Õ((q⁴/2ⁿ)^{1/6}) depends only on the number of queries (p.26); every QPT adversary is such a family
--   - encoding: A^{|O_n⟩}(1ⁿ, y) → the published BBBV.RandomOracle.QueryAlg A n y with XOR queries to O_n : Str n → Str n; reason: 1ⁿ is the index n; the input y is loaded into the initial state
-- source:
--   Liang, Yamakawa, Yung, Structured Quantum Hardness from Unstructured Assumptions, STOC 2027 submission (held manuscript, sha256 6464b75a…), Lemma 9, p.26 (PDF p.29), and its explanation

import Definitions.Def_QBennettGill_Negligible
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_BBBV_RandomOracle_QueryModel

set_option autoImplicit false

namespace QBennettGill

open BBBV.RandomOracle

/-- **Lemma 9** ([HXY19, Theorem 2]) for query-bounded adversaries: for every polynomial `q` and every
family of adversaries `A_n` with input `y ∈ {0,1}ⁿ` making `q(n)` quantum queries to `O_n : {0,1}ⁿ → {0,1}ⁿ`,
there is a negligible `negl` with
`|Pr[A^{|O_n⟩}(1ⁿ, O_n(x)) = 1 : x ←$ {0,1}ⁿ, O_n ← 𝒪_n] − Pr[A^{|O_n⟩}(1ⁿ, y) = 1 : y ←$ {0,1}ⁿ, O_n ← 𝒪_n]| ≤ negl(n)`.

Liang, Yamakawa, Yung, *Structured Quantum Hardness from Unstructured Assumptions*,
STOC 2027 submission (held manuscript, sha256 6464b75a…), Lemma 9, p.26 (PDF p.29), with the explanation following it.

**Formalization Note.** The adversary for length `n` and input `y` is a published `BBBV.RandomOracle.QueryAlg`
(arbitrary unit initial state, arbitrary unitaries, `q(n)` XOR queries to `O_n`); the input `1ⁿ` is the
index `n`. Every QPT adversary is such a family. -/
theorem lemma_9 (q : Polynomial ℕ) (W : ℕ → Type) [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)]
    (A : ∀ n : ℕ, Str n → QueryAlg (Str n) (Str n) (W n) (q.eval n)) :
    ∃ negl : ℕ → ℝ, Negligible negl ∧ ∀ n : ℕ,
      |NoSignalPA.uniformExp (fun On : Str n → Str n => NoSignalPA.uniformExp (fun x : Str n => acceptProb (A n (On x)) (fun _ => On))) -
        NoSignalPA.uniformExp (fun On : Str n → Str n => NoSignalPA.uniformExp (fun y : Str n => acceptProb (A n y) (fun _ => On)))| ≤
        negl n := by sorry

end QBennettGill
