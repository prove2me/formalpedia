-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanThesis_stabEncoder_encodes
-- name    : QAlgorithms.GottesmanThesis.stabEncoder_encodes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:59:10.414012+00:00
-- url     : https://prove2.me/theorems/1b8991be-8837-4124-b2f1-4a0a8aa3a361
-- title:
--   The standard-form encoding network maps |c⟩ to the encoded basis state (4.8)
-- statement:
--   Let a stabilizer on $n=m+k$ qubits ($m=n-k$ generators) be given in the standard form (4.3) of §4.1,
--   $$\left(\begin{array}{ccc|ccc} I & A_1 & A_2 & B & C_1 & C_2\\ 0 & 0 & 0 & D & I & E\end{array}\right),$$
--   with $r$ rows in the first block, and assume its rows commute: $H_xH_z^{\mathsf T}+H_zH_x^{\mathsf T}=0$. For a binary row $(a\,|\,b)$ write $P(a|b)=\bigotimes_q \sigma_z^{b_q}\sigma_x^{a_q}$ (the real form, sign $+1$). Let $M_i=P(\text{row } i)$ be the generators and let $\bar X_1,\dots,\bar X_k$ be the logical $\sigma_x$ operators in the standard form of p.40: $\bar X_i=P(0\,u_2\,e_i\,|\,v_1\,0\,0)$ with $u_2$ the $i$-th row of $E^{\mathsf T}$ and $v_1$ the $i$-th row of $E^{\mathsf T}C_1^{\mathsf T}+C_2^{\mathsf T}$.
--
--   Let $U_{\mathrm{enc}}$ be the encoding network of §4.2 (with the author's errata): first, for each $i$, the controlled-NOTs that apply $\bar X_i$ without its final $\sigma_x$, controlled on qubit $n-k+i$; then, for $i=1,\dots,r$ in turn, the Hadamard $R$ on qubit $i$, a $\sigma_z$ on qubit $i$ if $B_{ii}=1$, and $M_i$ without its qubit-$i$ factor, controlled on qubit $i$ (controlled-$\sigma_z^{b}\sigma_x^{a}$ gates). Then for every $c=c_1\dots c_k\in\{0,1\}^k$,
--   $$U_{\mathrm{enc}}\,|0\dots0\rangle|c_1\dots c_k\rangle=\frac{(I+M_1)\cdots(I+M_{n-k})\,\bar X_1^{c_1}\cdots\bar X_k^{c_k}|0\dots0\rangle}{\big\|(I+M_1)\cdots(I+M_{n-k})\,\bar X_1^{c_1}\cdots\bar X_k^{c_k}|0\dots0\rangle\big\|},$$
--   and in particular the vector on the right-hand side is nonzero.
--
--   This is the correctness of Gottesman's general encoding circuit for stabilizer codes: the network prepares exactly the encoded basis states, with no leftover global phase.
--
--   **Formalization Note** The errata are built in: the Hadamard on qubit $i$ comes just before that qubit's control operations, controlled-$Y$ gates are controlled-$\sigma_z\sigma_x$ gates in the real form, and every generator has sign $+1$. The page writes encoded states unnormalized; the unitary network yields the normalized vector. Since the real form $\sigma_z\sigma_x=i\sigma_y$, a generator with an odd number of $(1|1)$ positions is $i$ times a Hermitian Pauli operator; the identity is the one the page's network computes in this convention.
-- source:
--   Daniel Gottesman, Stabilizer Codes and Quantum Error Correction, 1997 thesis, downloaded arXiv v1 PDF; PDF title page now prints 2024, PDF p. 41, §4.2. https://arxiv.org/pdf/quant-ph/9705052v1

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
set_option autoImplicit false

namespace QAlgorithms.GottesmanThesis


/-- Gottesman thesis pp.41–43, §4.2 (unnumbered; equation (4.8)), with the author's errata:
for a stabilizer in standard form (4.3) with rank parameter `r` and commuting rows, and the
logical `X̄` operators in the standard form of p.40 (`U₃ = I`, `V₃ = 0`, `U₂ = Eᵀ`,
`V₁ = EᵀC₁ᵀ + C₂ᵀ`), the encoding network of §4.2 maps the input `|0…0⟩|c₁…c_k⟩` (the first
`n − k` qubits in `|0⟩`, `|c_i⟩` in qubit `n − k + i`) to the normalized encoded basis state
`(I + M₁)⋯(I + M_{n−k}) X̄₁^{c₁}⋯X̄_k^{c_k} |0…0⟩`.

The network (`stabEncoder`) is the controlled-NOT step (each `X̄_i` without its last `σx`,
controlled on qubit `n − k + i`), followed, for `i = 1, …, r` in turn, by `R` on qubit `i`, `σz`
on qubit `i` if `B_ii = 1`, and `M_i` (without its qubit-`i` factor) controlled on qubit `i`
(erratum: Hadamard just before the qubit's control dots). Generators and `X̄`'s are the
real-form Pauli products `σz^b σx^a` with sign `+1` (errata: controlled-`Y` is controlled-`XZ`;
the method needs every generator of sign `+1`). -/
theorem stabEncoder_encodes {m k r : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hstd : IsStandardForm r Hx Hz) (hcomm : SymplecticCommuting Hx Hz) (c : Qubits k) :
    act (stabEncoder r Hx Hz).unitary (ket (Fin.append (fun _ : Fin m => false) c)) =
      normalizedVec (stabEncodedState r Hx Hz c) := by
  sorry

end QAlgorithms.GottesmanThesis
