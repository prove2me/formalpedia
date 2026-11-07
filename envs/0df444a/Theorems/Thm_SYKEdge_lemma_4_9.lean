-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_9
-- name    : SYKEdge.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:24.473931+00:00
-- url     : https://prove2.me/theorems/d098d85e-3abf-4cdc-8692-57aeedac641f
-- title:
--   Lemma 4.9 — $\varphi(x^{2\ell})\le\big(4(1+(\rho^++\delta)\ell)/(1-(q-\rho^+)_+)\big)^\ell$
-- statement:
--   Let $\mathcal H$ be a $k$-uniform hypergraph with leakage parameters $q,\delta,\rho^+$, and write $\eta_+=\max\{\eta,0\}$. If $(q-\rho^+)_+<1$, then for every $\ell\ge0$ the vacuum moment $\varphi(x^{2\ell})$ is real and
--   $$\varphi(x^{2\ell})\le\left(\frac{4\big(1+(\rho^++\delta)\ell\big)}{1-(q-\rho^+)_+}\right)^{\ell}.$$
--
--   Combined with Proposition 4.7 this bounds $\mathbb E\operatorname{tr}H^{2\ell}$ and hence, by a moment argument, $\mathbb E\|H\|_{op}$.
--
--   **Formalization Note** $\varphi(x^{2\ell})$ is a complex number; the statement asserts that its imaginary part vanishes and bounds its real part.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: φ(x^{2ℓ}) ⩽ (real bound) → Im φ(x^{2ℓ}) = 0 and Re φ(x^{2ℓ}) ⩽ (real bound); reason: an inequality between a complex number and a real number asserts that the former is real
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.9, p.26

import Mathlib
import Definitions.Def_SYKEdge_Fock
import Definitions.Def_SYKEdge_SignMatrix
import Definitions.Def_SYKEdge_Hamiltonian

namespace SYKEdge

/-- **Lemma 4.9** (Spectral Bounds for `φ(x^{2ℓ})`), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.26.

If `(q − ρ⁺)₊ < 1` then `φ(x^{2ℓ}) ⩽ (4(1 + (ρ⁺ + δ)ℓ) / (1 − (q − ρ⁺)₊))^ℓ`.

**Formalization Note.** Stated for every `ℓ ∈ ℕ`. `φ(x^{2ℓ})` is a complex number; the page's
inequality asserts that it is real, so the statement has two parts: its imaginary part is `0` and its
real part is at most the bound. `η₊ = max{η, 0}` (p.15). -/
theorem lemma_4_9 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    (h : max (qParam S - rhoPlus S) 0 < 1) (ℓ : ℕ) :
    (fockPhi (xop S ^ (2 * ℓ))).im = 0 ∧
    (fockPhi (xop S ^ (2 * ℓ))).re ≤
      (4 * (1 + (rhoPlus S + deltaParam S) * ℓ) / (1 - max (qParam S - rhoPlus S) 0)) ^ ℓ := by sorry

end SYKEdge
