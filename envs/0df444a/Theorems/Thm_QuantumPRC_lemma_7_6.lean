-- Prove2me | Theorems.Thm_QuantumPRC_lemma_7_6
-- name    : QuantumPRC.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:27.7205+00:00
-- url     : https://prove2.me/theorems/d3f916b9-fc69-49a6-97e0-dd5f91da8802
-- title:
--   Lemma 7.6 — robustness of Construction 7.2 to every $w$-local noise
-- statement:
--   Let $n_{\mathrm P}=n_{\mathrm L}+\ell+r+m$ and assume the standing conditions of §7 (p.40): $n_{\mathrm P}$ is even for all sufficiently large $\lambda$; $0<p<1$ and $C\ge1$ with $n_{\mathrm P}\le Cm$ for all sufficiently large $\lambda$; $w=o(n_{\mathrm P}\log\log n_{\mathrm P}/\log n_{\mathrm P})$; $t(n)=o(n\log\log n/\log n)$ with $t(n_{\mathrm P}(\lambda)/2)\ge w(\lambda)$ for all sufficiently large $\lambda$. Assume $n_{\mathrm P}(\lambda)\ge\lambda^\kappa$ for some $\kappa>0$ and $n_{\mathrm P}=O(m)$. Consider Construction 7.2 with
--
--   1. an inner code whose decoder satisfies the PRFC robustness condition (80) for every $p$-bounded channel,
--   2. arbitrary keyed functions $f_k$ and permutations $\pi_{k'}$,
--   3. a graph sampler and decoder satisfying, at $n=\lfloor n_{\mathrm P}(\lambda)/2\rfloor$, the scheme parameter $W(\lambda)$ and radius $t(n)$, properties (i) and (ii) of Theorem 7.1 with constant $p_g=p/C$: every sampled graph has $\mathrm{wt}(v\oplus Au)\le p_g n$, and Recover returns $u$ with probability $\ge1-\nu(n)$, $\nu$ negligible, whenever $|\mathrm{supp}(u)\cup\mathrm{supp}(v)|\le t(n)$.
--
--   Then for every $w$-local noise family $\mathcal E$ (Definition 3.7), the key-averaged channel satisfies
--
--   $$
--   \big\|\mathbb E_{\mathsf{sk}}(\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\mathsf{sk}})-\mathrm{id}\big\|_\diamond\le\mathsf{negl}(\lambda).
--   $$
--
--   Differences from the source:
--   - generalization: an (nL + ℓ, m) PRFC robust to any p-bounded channel, a PRF F, a PRP Π, and GraphSample, Recover of Theorem 7.1 at p_g and t → any inner code with robustness (80) for every p-bounded channel, arbitrary keyed f_k and permutations π_{k′}, and any sampler/decoder with properties (i), (ii) at n = ⌊nP/2⌋ and radius t; reason: the robustness proof uses only these properties; the printed ingredients satisfy them (Theorem 7.1 at all large n implies them along n = ⌊nP(λ)/2⌋ since nP → ∞)
--   - encoding: Construction 7.2 for even nP → the construction is also defined for odd nP (graph on the first 2⌊nP/2⌋ vertices, last bit of the phase estimate 0); reason: Lean needs a total definition; nP is even for all large λ by hypothesis, and negl ignores finitely many λ
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Lemma 7.6, p.42; standing assumptions p.40; Construction 7.2, p.41

import Mathlib
import Definitions.Def_QuantumPRC_C72

open Filter Asymptotics

namespace QuantumPRC

open Classical in
/-- **Lemma 7.6** (robustness of Construction 7.2). Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), Lemma 7.6, p.42: "Let `w : ℕ → ℕ` be a function satisfying `w = o(nP log log nP / log nP)`. If
`nP(λ) ≥ λ^κ` for some constant `κ > 0` and `nP = O(m)`, then Construction 7.2, with the graph parameters
chosen above, satisfies robustness for any `w`-local error channel."

Standing assumptions, p.40: `nP := nL + ℓ + r + m`; "nP is even for all sufficiently large λ"; "Fix
constants `0 < p < 1` and `C ≥ 1` such that `nP ≤ Cm` for all sufficiently large λ", `p_g = p/C`, and `t`
with `t(n) = o(n log log n / log n)` and `t(nP(λ)/2) ≥ w(λ)` for all sufficiently large λ. Construction
7.2, p.41: the PRFC is robust to any `p`-bounded channel, and GraphSample, Recover are those of
Theorem 7.1 at `p_g` and `t`.

Here the PRFC is any keyed code with the robustness clause (80) for every `p`-bounded channel, the
keyed `f_k` and `π_{k′}` are arbitrary, and GraphSample / Recover are any sampler and decoder with
properties (i), (ii) of Theorem 7.1 at `p_g` and radius `t`, at the size `n = ⌊nP(λ)/2⌋` used by the
construction and the scheme parameter `W(λ)`.

**Formalization Note.** The conclusion is `ChScheme.Robust` (43) for every `w`-local noise family. -/
theorem lemma_7_6 (D : C72) (p C : ℝ) (hp : 0 < p) (hp1 : p < 1) (hC : 1 ≤ C)
    (hCm : ∀ᶠ lam in atTop, (D.nP lam : ℝ) ≤ C * D.m lam)
    (heven : ∀ᶠ lam in atTop, Even (D.nP lam))
    (w t : ℕ → ℕ)
    (hw : (fun lam => (w lam : ℝ)) =o[atTop]
      (fun lam => (D.nP lam : ℝ) * Real.log (Real.log (D.nP lam)) / Real.log (D.nP lam)))
    (ht : (fun n => (t n : ℝ)) =o[atTop] radiusScale)
    (htw : ∀ᶠ lam in atTop, w lam ≤ t (D.nP lam / 2))
    (hκ : ∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℕ, (lam : ℝ) ^ κ ≤ D.nP lam)
    (hO : (fun lam => (D.nP lam : ℝ)) =O[atTop] (fun lam => (D.m lam : ℝ)))
    (hprfc : ∀ E : CNoise D.m, IsPBounded p E → D.prfc.Robust E)
    (W : ℕ → ℕ)
    (hi : ∀ᶠ lam in atTop, ∀ u v : Bits (2 * (D.nP lam / 2)),
      suppUnionCard u v ≤ t (D.nP lam / 2) → ∀ ρ : Bits (D.gc (D.nP lam / 2)),
        (wt (xorB v (adjMul (D.gs (W lam) (D.nP lam / 2) ρ) u)) : ℝ) ≤ p / C * (D.nP lam / 2 : ℕ))
    (hii : ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ᶠ lam in atTop, ∀ u v : Bits (2 * (D.nP lam / 2)),
      suppUnionCard u v ≤ t (D.nP lam / 2) →
        1 - ν (D.nP lam / 2) ≤ avg fun ρ : Bits (D.gc (D.nP lam / 2)) =>
          if D.recv (W lam) (D.nP lam / 2) (D.gs (W lam) (D.nP lam / 2) ρ)
              (xorB v (adjMul (D.gs (W lam) (D.nP lam / 2) ρ) u)) = u then 1 else 0) :
    ∀ E : ∀ lam, WildeQIT.QChannel (Bits (D.nP lam)) (Bits (D.nP lam)),
      IsLocalNoise w D.nP E → D.scheme.Robust W E := by sorry

end QuantumPRC
