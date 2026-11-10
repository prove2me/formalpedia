-- Prove2me | Theorems.Thm_PPSLattice_homomorphic_evaluation
-- name    : PPSLattice.homomorphic_evaluation
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:36:25.849559+00:00
-- url     : https://prove2.me/theorems/c4943b58-67b7-4a79-b204-63ef15701a87
-- title:
--   §3.1 Homomorphic Computation — $(\mathbf B-\mathbf x^\top\otimes\mathbf G)\mathbf H_{f,x}=\mathbf B_f-f(x)\mathbf G$ and $\|\mathbf H_{f,x}\|\le m^{O(d)}$
-- statement:
--   There are deterministic polynomial-time algorithms $\mathrm{EvalF}$ and $\mathrm{EvalFX}$ and a constant $c$ such that for every prime $q$, all $n,m$ with $m\ge n\lceil\log q\rceil$, every $\ell$, every $\mathbf B\in\mathbb Z_q^{n\times\ell m}$, every single-output Boolean circuit $f$ on $\ell$ inputs of depth $d$ and every $\mathbf x\in\{0,1\}^\ell$,
--
--   1. $(\mathbf B-\mathbf x^\top\otimes\mathbf G)\mathbf H_{f,x}=\mathbf B_f-f(\mathbf x)\mathbf G$, where $\mathbf B_f=\mathrm{EvalF}(\mathbf B,f)$ and $\mathbf H_{f,x}=\mathrm{EvalFX}(\mathbf B,f,\mathbf x)$;
--   2. $\|\mathbf H_{f,x}\|\le m^{c(d+1)}$, independently of the size of $f$.
--
--   This is the [GSW13, BGG+14] machinery behind the digest $\mathbf A_S$ in KGen and the matrix $\mathbf H_{S,i}$ in Decode.
--
--   Differences from the source:
--   - encoding: m^{O(d)} → m^{c(d+1)} with one constant c; reason: agrees for d ≥ 1 and stays meaningful at depth 0
--   - encoding: f ∈ F_{d,ℓ} → a single-output NAND circuit on ℓ inputs whose depth is d; reason: F_{d,ℓ} is defined by depth-d Boolean circuits
--   - reading: ‖H‖, the maximum of the entries → largest absolute value of the centered representatives; reason: the standard meaning for noise bounds over Z_q
--   - reading: Z_q for (prime power) q, LWE parameters (n, m, q) → q prime, Z_q = ZMod q; reason: the paper's LWE moduli are prime (§4.3, Remark 4.9), where ZMod q is the field with q elements
--   - reading: two deterministic polynomial-time algorithms → HomEval.Efficient: one polynomial-time machine each, on (q in binary, 1^n, 1^m, 1^ℓ, B, f); reason: §3.1, p.16
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, properties (1)–(2), pp.16–17

import Mathlib
import Definitions.Def_PPSLattice_HomEval_Efficient
import Definitions.Def_PPSLattice_HomEval_Valid
set_option autoImplicit false

namespace PPSLattice

/-- **Homomorphic computation** ([GSW13, BGG+14]). There are deterministic polynomial-time algorithms
EvalF and EvalFX and a constant `c` such that, for every prime `q`, all `n, m` with `m ≥ n⌈log q⌉`, every
`B ∈ Z_q^{n×ℓm}`, every single-output circuit `f` on `ℓ` inputs of depth `d` and every `x ∈ {0,1}^ℓ`:
(1) `(B − x^⊤ ⊗ G) H_{f,x} = B_f − f(x) G` and (2) `‖H_{f,x}‖ ≤ m^{c(d+1)}`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, properties (1)–(2), pp.16–17. -/
theorem homomorphic_evaluation : ∃ H : HomEval, ∃ c : ℕ, H.Efficient ∧ H.Valid c := by sorry

end PPSLattice
