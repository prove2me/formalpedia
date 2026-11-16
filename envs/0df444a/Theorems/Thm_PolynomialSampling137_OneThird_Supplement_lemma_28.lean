-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_28
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:55:22.008074+00:00
-- url     : https://prove2.me/theorems/944c8452-2f16-4d80-82bd-4b21435691cf
-- title:
--   Lemma 28 — Signed dyadic acceptance representation with at most 2^q terms and arbitrary integer exponents
-- statement:
--   For every $q,s\ge0$ and every $f:\mathbb F_2^s\to\mathbb F_2$ computable by a circuit with at most $q$ distinct nonlinear ancestor gates,
--   $$\Pr[f(U_s)=1]=\sum_{i=1}^{\ell}\sigma_i2^{j_i},\quad\ell\le2^q,\quad\sigma_i\in\{-1,1\},\quad j_i\in\mathbb Z.$$
--   Exponents may be positive, repetitions are allowed, and the sum may be empty. This is a consequence of structural circuit membership, not its definition.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 28, printed p. 36; PDF p. 38

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Circuits

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_28 {s : ℕ} (q : ℕ) (f : Word s → ZMod 2)
    (hf : InCircuitClass q f) : SignedDyadic (2 ^ q) (acceptance f) := by sorry

end PolynomialSampling137.OneThird.Supplement
