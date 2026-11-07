-- Prove2me | Theorems.Thm_QuantumPRC_theorem_7_3
-- name    : QuantumPRC.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:17.901925+00:00
-- url     : https://prove2.me/theorems/26409495-4cd2-405a-8577-b1470067af24
-- title:
--   Theorem 7.3 — Construction 7.2 is a PRIC robust to every $w$-local noise
-- statement:
--   Let $n_{\mathrm L},\ell,r,m$ be efficient polynomial lengths, $n_{\mathrm P}=n_{\mathrm L}+\ell+r+m$, even for all sufficiently large $\lambda$, and fix $0<p<1$ and $C\ge1$ with $n_{\mathrm P}\le Cm$ for all sufficiently large $\lambda$. Assume $n_{\mathrm P}(\lambda)\ge\lambda^\kappa$ for some $\kappa>0$, $r\ge n_{\mathrm L}+\ell+\omega(\log\lambda)$, $\ell=\omega(\log\lambda)$ and $n_{\mathrm P}=O(m)$. Instantiate Construction 7.2 with an $(n_{\mathrm L}+\ell,m)$ PRFC robust to every $p$-bounded channel, a PRF $F$ with one output bit, a PRP $\Pi$ on $n_{\mathrm L}+\ell+r$ bits, and GraphSample, Recover as in Theorem 7.1 with constant $p/C$ (reading the scheme parameter as their radius). Then
--
--   1. the construction is implementable: KeyGen is PPT and Enc, Dec are uniform QPT;
--   2. for every $w:\mathbb N\to\mathbb N$ with $w=o(n_{\mathrm P}\log\log n_{\mathrm P}/\log n_{\mathrm P})$, run at the parameter $W=\min(w,n_{\mathrm P})$, it is a PRIC robust to every $w$-local noise (Definition 4.4).
--
--   Differences from the source:
--   - reading: let w = o(nP log log nP/log nP); Construction 7.2, with the graph parameters chosen for w, is a PRIC robust to w-local noise → one construction whose algorithms read 1^{min(w, nP)}; for every such w it is a PRIC at that parameter; reason: the graph parameters depend on w only through this value; for w computable in polynomial time it gives the printed statement (paper.md decision 4)
--   - reading: GraphSample and Recover from Theorem 7.1 → the machines of corrected Theorem 7.1 (GraphRecoverSpec), reading the radius in unary; reason: Theorem 7.1 as printed cannot hold for uncomputable radius functions (see its corrected item)
--   - generalization: n, m (or nL, nP, ℓ, r, m) are polynomials → they are EffPoly lengths: polynomially bounded and computable from 1^λ in polynomial time; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (paper.md decision 2)
--   - reading: QPT algorithm / QPT adversary (no machine model given) → uniform families of Clifford+T oracle circuits printed by a polynomial-time Turing machine; PPT algorithms are polynomial-time functions of polynomially many fair coins; reason: the paper fixes no model; this one covers adaptive and reference-entangled queries and is used on both sides of every implication (paper.md decision 3)
--   - encoding: the Haar measure µ_{nL→nP} on isometries → V = U·ι with U Haar on U(2^{nP}) (QAlgorithms.Schur.unitaryHaar) and ι|x⟩ = |x⟩|0^{nP−nL}⟩; reason: the realization used on p.69 of the paper; same law
--   - encoding: Construction 7.2 for even nP → the construction is also defined for odd nP (graph on the first 2⌊nP/2⌋ vertices, last bit of the phase estimate 0); reason: Lean needs a total definition; nP is even for all large λ by hypothesis, and negl ignores finitely many λ
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 7.3, p.42; standing assumptions p.40; Construction 7.2, p.41

import Mathlib
import Definitions.Def_QuantumPRC_C72

open Filter Asymptotics

namespace QuantumPRC

open Classical in
/-- **Theorem 7.3** (Construction 7.2 is a PRIC). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
Theorem 7.3, p.42: "Let `w : ℕ → ℕ` be a function satisfying `w = o(nP log log nP / log nP)`. If
`nP(λ) ≥ λ^κ` for some constant `κ > 0`, `r ≥ nL + ℓ + ω(log λ)`, `ℓ ≥ ω(log λ)`, and `nP = O(m)`, then
Construction 7.2, with the graph parameters chosen above, is a PRIC robust to any `w`-local noise."

Standing assumptions, p.40: `nL, ℓ, r, m` polynomials, `nP := nL + ℓ + r + m` even for all
sufficiently large λ, constants `0 < p < 1` and `C ≥ 1` with `nP ≤ Cm` for all sufficiently large λ,
`p_g = p/C`. Construction 7.2, p.41: an `(nL + ℓ, m)` PRFC robust to any `p`-bounded channel, a PRF
`F : {0,1}^λ × {0,1}^{nL+ℓ} → {0,1}`, a PRP `Π` on `{0,1}^{nL+ℓ+r}`, and GraphSample, Recover from
Theorem 7.1 at `p_g`.

**Formalization Note.** GraphSample and Recover are the machines of Theorem 7.1 in the form
`GraphRecoverSpec (p/C)`; they read the scheme parameter `W` as the radius. One construction serves
every `w`: it is run at `W = min(w, nP)` (`ChScheme.IsPRICAt`). "Is a PRIC" includes implementability
(KeyGen PPT; Enc, Dec uniform QPT). -/
theorem theorem_7_3 (D : C72) (F : PRF (fun lam => D.nL lam + D.ℓ lam) (fun _ => 1))
    (Pm : PRP (fun lam => D.nL lam + D.ℓ lam + D.r lam))
    (p C : ℝ) (hp : 0 < p) (hp1 : p < 1) (hC : 1 ≤ C)
    (hCm : ∀ᶠ lam in atTop, (D.nP lam : ℝ) ≤ C * D.m lam)
    (heven : ∀ᶠ lam in atTop, Even (D.nP lam))
    (hnL : EffPoly D.nL) (hℓ : EffPoly D.ℓ) (hr : EffPoly D.r) (hm : EffPoly D.m)
    (hf : ∀ lam k x, D.f lam k x = F.F lam k x 0)
    (hπ : ∀ lam k, ⇑(D.perm lam k) = Pm.P lam k)
    (hprfc : ∀ E : CNoise D.m, IsPBounded p E → D.prfc.IsPRFC E) (hF : F.IsPRF) (hP : Pm.IsPRP)
    (GS Rec : List Bool → List Bool) (hspec : GraphRecoverSpec (p / C) D.gc GS Rec)
    (hgs : ∀ T n ρ, D.gs T n ρ = graphOfCode (2 * n) (GS (tupleCode [unary n, unary T, bits ρ])))
    (hrec : ∀ T n (G : SimpleGraph (Fin (2 * n))) e,
      D.recv T n G e = fun i => (Rec (tupleCode [unary T, adjCode G, bits e])).getD i.val false)
    (hκ : ∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℕ, (lam : ℝ) ^ κ ≤ D.nP lam)
    (hrω : SuperLog fun lam => (D.r lam : ℝ) - D.nL lam - D.ℓ lam)
    (hℓω : SuperLog fun lam => (D.ℓ lam : ℝ))
    (hO : (fun lam => (D.nP lam : ℝ)) =O[atTop] (fun lam => (D.m lam : ℝ))) :
    D.scheme.Implementable ∧
      ∀ w : ℕ → ℕ,
        (fun lam => (w lam : ℝ)) =o[atTop]
          (fun lam => (D.nP lam : ℝ) * Real.log (Real.log (D.nP lam)) / Real.log (D.nP lam)) →
        D.scheme.IsPRICAt w := by sorry

end QuantumPRC
