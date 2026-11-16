-- Prove2me | Theorems.Thm_PolyTimeMBLG_Monotone_Supplement_lemma_15
-- name    : PolyTimeMBLG.Monotone.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:35:17.391685+00:00
-- url     : https://prove2.me/theorems/fed6662e-b615-419d-a521-056f3a75eec1
-- title:
--   Lemma 15 — open-regime generation for all polynomial-size circuits rules out one-way functions
-- statement:
--   Suppose that for every polynomial $p$, the family of $p(n)$-size circuits is polynomial-time MBLG in the open regime: for each $p$ there are a polynomial $e$ and a polynomial-time open-regime generator that, given a circuit $C$ on $n$ inputs with at most $p(n)$ gates and the distinct satisfying assignments of $C$ printed so far, makes at most $e(n)$ mistakes on every enumeration of $C^{-1}(1)$, for every $n\ge1$. Then one-way functions do not exist:
--   $$\bigl(\forall p:\ p(n)\text{-size circuits are polynomial-time MBLG in the open regime}\bigr)\ \Longrightarrow\ \neg\,\exists f\ \text{one-way}.$$
--
--   Here $f:\{0,1\}^*\to\{0,1\}^*$ is one-way (Definition 21) if it is polynomial-time computable and no polynomial-time randomized algorithm, given $1^n$ and $f(x)$ for uniform $x\in\{0,1\}^n$, returns some $\hat x\in\{0,1\}^n$ with $f(\hat x)=f(x)$ with probability at least $1/\mathrm{poly}(n)$ for infinitely many $n$.
--
--   This is the last step of the proof of Theorem 3. The paper's proof uses a strong chosen-message forger built from the generator and the existence of strongly unforgeable signature schemes under one-way functions (Katz, Theorem 3.5); that external result is part of the proof, not an assumption.
--
--   **Formalization Note** The generator and mistake polynomial may depend on $p$. Circuits, the open regime and one-way functions are this mission's definitions.
--
--   Differences from the source:
--   - encoding: "for any polynomial $p(n)$" → every $p$ with natural coefficients; reason: every real polynomial is bounded on $\mathbb N$ by one with natural coefficients, and generation for a larger size cap implies it for a smaller one, so the hypothesis is the same.
--   - encoding: the paper's unspecified circuit model → fan-in-two AND/OR gates and NOT gates, size = number of gates, no constant gates; reason: the paper fixes no model, and standard models are polynomially related, so the quantification over all polynomials $p$ means the same.
--   - encoding: polynomial-time MBLG in the open regime → a polynomial-time machine on the encoded input (circuit code, then $1^n$ and the words), polynomial mistake bound, without the size condition of Definition 6; reason: the encoded input length is polynomial in $n(i+1)$ for circuits of size at most $p(n)$, and the size condition always holds for these families.
--   - encoding: polynomial-time randomized inverter → a polynomial-time TM2 machine on $(1^n, f(x))$ and a coin string of length $c(n)$ for a polynomial $c$, with success probability the exact fraction of pairs $(x,r)$; reason: the length of $f(x)$ is polynomial in $n$, so polynomially many coins and polynomial time in the input length are the standard notions.
--   - encoding: "with probability $1/\mathrm{poly}(n)$" → $1\le q(n)\cdot\Pr[\text{success}]$ for a polynomial $q$ with natural coefficients; reason: every positive inverse-polynomial lower bound is of this form.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Lemma 15, p. 9, proof pp. 9–10; open regime, p. 9; Definition 21, p. 13. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Supplement_OpenRegime
import Definitions.Def_PolyTimeMBLG_Monotone_Supplement_OneWay

namespace PolyTimeMBLG.Monotone.Supplement

/-- Lemma 15, pp. 9–10: if for every polynomial `p` the family of `p(n)`-size circuits is
polynomial-time MBLG in the open regime, then no one-way function (Definition 21, p. 13) exists. -/
theorem lemma_15 (h : ∀ p : Polynomial ℕ, IsOpenPolyTimeMBLG p) :
    ¬ ∃ f : List Bool → List Bool, IsOneWay f := by sorry

end PolyTimeMBLG.Monotone.Supplement
