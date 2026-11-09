-- Prove2me | Theorems.Thm_PermutationStreams_Parity_sign_correlation
-- name    : PermutationStreams.Parity.sign_correlation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:11.575442+00:00
-- url     : https://prove2.me/theorems/516fb3c8-574b-435d-8f98-843696990541
-- title:
--   Lemma 4.3 — product of local permutation signs has exponentially small correlation
-- statement:
--   Let $\mu$ be the uniform distribution on the six permutations of $(1,2,3)$ and $f_m(x,y,z)=\prod_{i=1}^m\varepsilon(x_i,y_i,z_i)$ the product of the local signs. There is an absolute constant $\alpha>0$ such that for all $m\ge1$ and all $F,G,H:[3]^m\to D$,
--
--   $$
--   \Bigl|\ \mathbb E_{\mu^{\otimes m}}\bigl[f_m(x,y,z)\,F(x)\,G(y)\,H(z)\bigr]\Bigr|\le 2^{-\alpha m}.
--   $$
--
--   Taking $F,G,H$ to be indicators, this bounds the correlation of $f_m$ with every combinatorial rectangle, which is the input to the communication lower bound of Lemma 4.4.
--
--   **Formalization Note** The inequality is the predicate `SignCorrelationBound α`; the lemma asserts it for some $\alpha>0$. $[3]$ is encoded as $\{0,1,2\}$.
--
--   Differences from the source:
--   - encoding: [3] = {1,2,3}, coordinates 1,…,m → Fin 3, Fin m; reason: order-preserving relabelling
--   - encoding: uniform distribution µ on the six permutations, expectation under µ^⊗m → the point-mass function mu6, expectation the finite weighted sum prodExpect; reason: the same law and the same expectation on a finite set
--   - encoding: F, G, H : [3]^m → D → complex-valued functions with norm at most 1; reason: D is the closed unit disk
--   - encoding: ε and f_m defined on promised triples, with values ±1 → ε and f_m defined on all triples by the same formula, as units of ℤ cast to ℂ; reason: unpromised triples have probability zero
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §4.2, p. 6, Lemma 4.3

import Definitions.Def_PermutationStreams_Parity_SignProblem

namespace PermutationStreams.Parity

/-- Braverman–Zamir, Lemma 4.3, p.6: there is an absolute constant `α > 0` such that for all
`m ≥ 1` and all `F, G, H : [3]^m → D`,
`|E_{μ^{⊗m}}[f_m(x, y, z) F(x) G(y) H(z)]| ≤ 2^{-αm}`, with `μ` uniform on the six
permutations of `(1, 2, 3)`. (`SignCorrelationBound α` spells out this inequality.) -/
theorem sign_correlation : ∃ α : ℝ, 0 < α ∧ SignCorrelationBound α := by sorry

end PermutationStreams.Parity
