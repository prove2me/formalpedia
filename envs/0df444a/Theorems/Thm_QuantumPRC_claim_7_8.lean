-- Prove2me | Theorems.Thm_QuantumPRC_claim_7_8
-- name    : QuantumPRC.claim_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:11.697007+00:00
-- url     : https://prove2.me/theorems/094158ef-40c7-4577-8b7f-c522d5cc72c9
-- title:
--   Claim 7.8 (corrected: global phase $(-1)^{q_G(u)}$) — action of BitDec on a Pauli-corrupted CWS codeword
-- statement:
--   Let $n_{\mathrm L},\ell,r,m\in\mathbb N$, $n_{\mathrm P}=n_{\mathrm L}+\ell+r+m$, and let $f:\{0,1\}^{n_{\mathrm L}+\ell}\to\{0,1\}$, a permutation $\pi$ of $\{0,1\}^{n_{\mathrm L}+\ell+r}$, $g:\{0,1\}^{n_{\mathrm L}+\ell}\to\{0,1\}^m$ and $\mathrm{Dec}:\{0,1\}^m\to\{0,1\}^{n_{\mathrm L}+\ell}$ be arbitrary, with $V_{\mathsf{sk}_{\mathrm{in}}}$ and $\mathsf{BitDec}$ built from them as in Construction 7.2. Let $G$ be any simple graph on $[n_{\mathrm P}]$ with adjacency matrix $A$, let $u,v\in\{0,1\}^{n_{\mathrm P}}$, $e=v\oplus Au$, $e_1$ the last $m$ bits of $e$, and $c(z)=\pi(z\|0^r)\|g(z)$. Then for every $x\in\{0,1\}^{n_{\mathrm L}}$,
--
--   $$
--   \Pi^{\mathsf{Good}}_{BCD}\,\mathsf{BitDec}\,(U_G^\dagger Z^vX^uU_G)\,V_{\mathsf{sk}_{\mathrm{in}}}|x\rangle
--   =(-1)^{q_G(u)}\,|e\rangle_{BC}\otimes\Big(\frac1{\sqrt{2^\ell}}\sum_{y:\ \mathrm{Dec}(g(x\|y)\oplus e_1)=x\|y}(-1)^{u\cdot c(x\|y)}|x\|y\rangle_D\Big).
--   $$
--
--   The good component of the decoded state carries the bit error $e$ in $BC$ and the phase $(-1)^{u\cdot c}$ in $D$, which Recover and the final phase correction remove; the global sign does not affect the density operator, so Lemma 7.6 is unaffected.
--
--   Differences from the source:
--   - correction: the right side of (137) has no global sign → the right side is multiplied by (−1)^{q_G(u)}; reason: the proof's first step (138) uses Lemma 3.15 without its sign (−1)^{q_G(u)}; counterexample: n_L = ℓ = r = m = 1, π = id, f ≡ 0, g ≡ 0, Dec ≡ 00, the graph with the single edge {1, 2}, u = 1100, v = 0000, x = 0: then q_G(u) = 1, e = 1100, and the (e, 00) entry is −1/√2 on the left and +1/√2 on the printed right side (checked numerically; 20480 random cases agree with the corrected form, paper.md decisions 11–12)
--   - generalization: keyed f_k, π_{k′}, g_{sk′} = PRFC.Enc(sk′, ·), PRFC.Dec(sk′, ·) and a sampled bipartite graph → arbitrary functions f, g, Dec, an arbitrary permutation π and an arbitrary simple graph on the n_P physical qubits; reason: the claim is a linear-algebra identity; the keyed objects and the sampled graphs are special cases
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Claim 7.8, Eq. (137), p.44 (proof pp.45, (138)–(142)); Eq. (126), p.43; Construction 7.2, p.41

import Mathlib
import Definitions.Def_QuantumPRC_C72

open Matrix

namespace QuantumPRC

/-- **Claim 7.8** (corrected: global phase `(−1)^{q_G(u)}`). Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), Claim 7.8, p.44: "For any `x ∈ {0,1}^{nL}`, `Π^Good_{BCD} · BitDec_{sk_in,BC→BCD} ·
(U_G† Z^v X^u U_G) · Enc_{sk_in,A→BC} · |x⟩_A = |e⟩_{BC} ⊗ ((1/√2^ℓ) Σ_{y : PRFC.Dec(sk′, g_{sk′}(x∥y)⊕e₁)=x∥y}
(−1)^{u·c(x∥y)} |x∥y⟩_D)`, where `c(z) := π_{k′}(z∥0^r)∥g_{sk′}(z)` and `e₁` denotes the last `m` bits of
`e = v ⊕ Au`."

Stated for arbitrary `f`, `π`, `g`, an arbitrary decoder `dec` and an arbitrary simple graph on the
`nL + ℓ + r + m` physical qubits; the right side carries the factor `(−1)^{q_G(u)}` of Lemma 3.15.

**Formalization Note.** Vectors on `BCD` are functions of `(s, z)` with `s` the `BC` string and `z`
the `D` string; `Enc_{sk_in}` is `vSkin`, `BitDec` is `bitDec`, `Π^Good` is `piGood e`. -/
theorem claim_7_8 {nL ℓ r m : ℕ} (f : Bits (nL + ℓ) → Bool) (π : Equiv.Perm (Bits (nL + ℓ + r)))
    (g : Bits (nL + ℓ) → Bits m) (dec : Bits m → Bits (nL + ℓ))
    (G : SimpleGraph (Fin (nL + ℓ + r + m))) [DecidableRel G.Adj] (u v : Bits (nL + ℓ + r + m))
    (x : Bits nL) :
    let e := xorB v (adjMul G u)
    piGood e *ᵥ (bitDec f π g dec *ᵥ
        (((graphUnitary G)ᴴ * (pauliZ v * pauliX u) * graphUnitary G) *ᵥ
          (vSkin f π g *ᵥ fun x' => if x' = x then 1 else 0))) =
      ((-1 : ℂ) ^ qG G u) • fun q : Bits (nL + ℓ + r + m) × Bits (nL + ℓ) =>
        if q.1 = e then
          ((Real.sqrt 2 : ℂ) ^ ℓ)⁻¹ * ∑ y : Bits ℓ,
            if q.2 = Fin.append x y ∧ dec (xorB (g (Fin.append x y)) (rightPart e)) = Fin.append x y then
              (if dotB u (cwVec π g (Fin.append x y)) then -1 else 1)
            else 0
        else 0 := by sorry

end QuantumPRC
